import V185TrunkScan23Chunk0982

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5819389 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_5819389 : Nat := 118140960795 + 5819389 * 2 ^ 59
def prefixEnd_5819389 : Nat := 4983230072969 + 3 ^ 40 * 5819389 * 2
def baseEnd_5819389 : Nat := 996047890829145782491541

theorem tailTrace_5819389 : CollatzResearch.WordTrace tailWord_5819389 prefixEnd_5819389 996047890829145782491541 := by
  unfold tailWord_5819389
  simp only [CollatzResearch.WordTrace]
  refine ⟨212250553914355000360077221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141500369276236666906718147 212250553914355000360077221)
  ·
    refine ⟨39796978858941562567514479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212250553914355000360077221 39796978858941562567514479)
    ·
      refine ⟨59695468288412343851271719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39796978858941562567514479 59695468288412343851271719)
      ·
        refine ⟨89543202432618515776907579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59695468288412343851271719 89543202432618515776907579)
        ·
          refine ⟨134314803648927773665361369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89543202432618515776907579 134314803648927773665361369)
          ·
            refine ⟨100736102736695830249021027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134314803648927773665361369 100736102736695830249021027)
            ·
              refine ⟨151104154105043745373531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100736102736695830249021027 151104154105043745373531541)
              ·
                refine ⟨7083007223673925564384291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151104154105043745373531541 7083007223673925564384291)
                ·
                  refine ⟨10624510835510888346576437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083007223673925564384291 10624510835510888346576437)
                  ·
                    refine ⟨996047890829145782491541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10624510835510888346576437 996047890829145782491541)
                    ·
                      rfl

theorem cell23_5819389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_5819389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819389 prefixEnd_5819389 := by exact prefixLift 5819389
  have htrace : WordTrace (prefixWord ++ tailWord_5819389) baseStart_5819389 baseEnd_5819389 := by
    simpa [prefixWord, tailWord_5819389, baseEnd_5819389] using wordTrace_append hprefix tailTrace_5819389
  have hstable : (prefixWord ++ tailWord_5819389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819389).length < 2 ^ (prefixWord ++ tailWord_5819389).sum := by decide
  have hdescent : baseEnd_5819389 < baseStart_5819389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819390 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5819390 : Nat := 118140960795 + 5819390 * 2 ^ 59
def prefixEnd_5819390 : Nat := 4983230072969 + 3 ^ 40 * 5819390 * 2
def baseEnd_5819390 : Nat := 2988144185968091843562119

theorem tailTrace_5819390 : CollatzResearch.WordTrace tailWord_5819390 prefixEnd_5819390 2988144185968091843562119 := by
  unfold tailWord_5819390
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531323798418922191357953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141500393591567585020575749 26531323798418922191357953)
  ·
    refine ⟨19898492848814191643518465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26531323798418922191357953 19898492848814191643518465)
    ·
      refine ⟨14923869636610643732638849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19898492848814191643518465 14923869636610643732638849)
      ·
        refine ⟨11192902227457982799479137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14923869636610643732638849 11192902227457982799479137)
        ·
          refine ⟨8394676670593487099609353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11192902227457982799479137 8394676670593487099609353)
          ·
            refine ⟨6296007502945115324707015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8394676670593487099609353 6296007502945115324707015)
            ·
              refine ⟨9444011254417672987060523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296007502945115324707015 9444011254417672987060523)
              ·
                refine ⟨14166016881626509480590785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444011254417672987060523 14166016881626509480590785)
                ·
                  refine ⟨10624512661219882110443089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14166016881626509480590785 10624512661219882110443089)
                  ·
                    refine ⟨7968384495914911582832317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10624512661219882110443089 7968384495914911582832317)
                    ·
                      refine ⟨2988144185968091843562119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968384495914911582832317 2988144185968091843562119)
                      ·
                        rfl

theorem cell23_5819390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5819390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819390 prefixEnd_5819390 := by exact prefixLift 5819390
  have htrace : WordTrace (prefixWord ++ tailWord_5819390) baseStart_5819390 baseEnd_5819390 := by
    simpa [prefixWord, tailWord_5819390, baseEnd_5819390] using wordTrace_append hprefix tailTrace_5819390
  have hstable : (prefixWord ++ tailWord_5819390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819390).length < 2 ^ (prefixWord ++ tailWord_5819390).sum := by decide
  have hdescent : baseEnd_5819390 < baseStart_5819390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819403 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 1, 1, 3]
def baseStart_5819403 : Nat := 118140960795 + 5819403 * 2 ^ 59
def prefixEnd_5819403 : Nat := 4983230072969 + 3 ^ 40 * 5819403 * 2
def baseEnd_5819403 : Nat := 2988150861216600292699559

theorem tailTrace_5819403 : CollatzResearch.WordTrace tailWord_5819403 prefixEnd_5819403 2988150861216600292699559 := by
  unfold tailWord_5819403
  simp only [CollatzResearch.WordTrace]
  refine ⟨212251064536304280751086863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141500709690869520500724575 212251064536304280751086863)
  ·
    refine ⟨318376596804456421126630295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212251064536304280751086863 318376596804456421126630295)
    ·
      refine ⟨477564895206684631689945443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318376596804456421126630295 477564895206684631689945443)
      ·
        refine ⟨716347342810026947534918165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477564895206684631689945443 716347342810026947534918165)
        ·
          refine ⟨33578781694220013165699289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 716347342810026947534918165 33578781694220013165699289)
          ·
            refine ⟨25184086270665009874274467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33578781694220013165699289 25184086270665009874274467)
            ·
              refine ⟨37776129405997514811411701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25184086270665009874274467 37776129405997514811411701)
              ·
                refine ⟨3541512131812267013569847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37776129405997514811411701 3541512131812267013569847)
                ·
                  refine ⟨5312268197718400520354771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541512131812267013569847 5312268197718400520354771)
                  ·
                    refine ⟨7968402296577600780532157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312268197718400520354771 7968402296577600780532157)
                    ·
                      refine ⟨2988150861216600292699559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968402296577600780532157 2988150861216600292699559)
                      ·
                        rfl

theorem cell23_5819403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 1, 3].length) (baseStart_5819403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819403 prefixEnd_5819403 := by exact prefixLift 5819403
  have htrace : WordTrace (prefixWord ++ tailWord_5819403) baseStart_5819403 baseEnd_5819403 := by
    simpa [prefixWord, tailWord_5819403, baseEnd_5819403] using wordTrace_append hprefix tailTrace_5819403
  have hstable : (prefixWord ++ tailWord_5819403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819403).length < 2 ^ (prefixWord ++ tailWord_5819403).sum := by decide
  have hdescent : baseEnd_5819403 < baseStart_5819403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819406 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_5819406 : Nat := 118140960795 + 5819406 * 2 ^ 59
def prefixEnd_5819406 : Nat := 4983230072969 + 3 ^ 40 * 5819406 * 2
def baseEnd_5819406 : Nat := 996050800552854593654015

theorem tailTrace_5819406 : CollatzResearch.WordTrace tailWord_5819406 prefixEnd_5819406 996050800552854593654015 := by
  unfold tailWord_5819406
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531396744411676532930759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141500782636862274842297381 26531396744411676532930759)
  ·
    refine ⟨39797095116617514799396139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26531396744411676532930759 39797095116617514799396139)
    ·
      refine ⟨59695642674926272199094209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39797095116617514799396139 59695642674926272199094209)
      ·
        refine ⟨44771732006194704149320657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59695642674926272199094209 44771732006194704149320657)
        ·
          refine ⟨33578799004646028111990493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44771732006194704149320657 33578799004646028111990493)
          ·
            refine ⟨12592049626742260541996435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33578799004646028111990493 12592049626742260541996435)
            ·
              refine ⟨18888074440113390812994653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12592049626742260541996435 18888074440113390812994653)
              ·
                refine ⟨7083027915042521554872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18888074440113390812994653 7083027915042521554872995)
                ·
                  refine ⟨10624541872563782332309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083027915042521554872995 10624541872563782332309493)
                  ·
                    refine ⟨996050800552854593654015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10624541872563782332309493 996050800552854593654015)
                    ·
                      rfl

theorem cell23_5819406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_5819406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819406 prefixEnd_5819406 := by exact prefixLift 5819406
  have htrace : WordTrace (prefixWord ++ tailWord_5819406) baseStart_5819406 baseEnd_5819406 := by
    simpa [prefixWord, tailWord_5819406, baseEnd_5819406] using wordTrace_append hprefix tailTrace_5819406
  have hstable : (prefixWord ++ tailWord_5819406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819406).length < 2 ^ (prefixWord ++ tailWord_5819406).sum := by decide
  have hdescent : baseEnd_5819406 < baseStart_5819406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819409 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_5819409 : Nat := 118140960795 + 5819409 * 2 ^ 59
def prefixEnd_5819409 : Nat := 4983230072969 + 3 ^ 40 * 5819409 * 2
def baseEnd_5819409 : Nat := 2988153942100527269224531

theorem tailTrace_5819409 : CollatzResearch.WordTrace tailWord_5819409 prefixEnd_5819409 2988153942100527269224531 := by
  unfold tailWord_5819409
  simp only [CollatzResearch.WordTrace]
  refine ⟨212251283374282543775805281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141500855582855029183870187 212251283374282543775805281)
  ·
    refine ⟨159188462530711907831853961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212251283374282543775805281 159188462530711907831853961)
    ·
      refine ⟨119391346898033930873890471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159188462530711907831853961 119391346898033930873890471)
      ·
        refine ⟨179087020347050896310835707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119391346898033930873890471 179087020347050896310835707)
        ·
          refine ⟨268630530520576344466253561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179087020347050896310835707 268630530520576344466253561)
          ·
            refine ⟨201472897890432258349690171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268630530520576344466253561 201472897890432258349690171)
            ·
              refine ⟨302209346835648387524535257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201472897890432258349690171 302209346835648387524535257)
              ·
                refine ⟨226657010126736290643401443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302209346835648387524535257 226657010126736290643401443)
                ·
                  refine ⟨339985515190104435965102165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226657010126736290643401443 339985515190104435965102165)
                  ·
                    refine ⟨3984205256134036358966041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 339985515190104435965102165 3984205256134036358966041)
                    ·
                      refine ⟨2988153942100527269224531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984205256134036358966041 2988153942100527269224531)
                      ·
                        rfl

theorem cell23_5819409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_5819409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819409 prefixEnd_5819409 := by exact prefixLift 5819409
  have htrace : WordTrace (prefixWord ++ tailWord_5819409) baseStart_5819409 baseEnd_5819409 := by
    simpa [prefixWord, tailWord_5819409, baseEnd_5819409] using wordTrace_append hprefix tailTrace_5819409
  have hstable : (prefixWord ++ tailWord_5819409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819409).length < 2 ^ (prefixWord ++ tailWord_5819409).sum := by decide
  have hdescent : baseEnd_5819409 < baseStart_5819409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819429 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_5819429 : Nat := 118140960795 + 5819429 * 2 ^ 59
def prefixEnd_5819429 : Nat := 4983230072969 + 3 ^ 40 * 5819429 * 2
def baseEnd_5819429 : Nat := 2988164211713617190974439

theorem tailTrace_5819429 : CollatzResearch.WordTrace tailWord_5819429 prefixEnd_5819429 2988164211713617190974439 := by
  unfold tailWord_5819429
  simp only [CollatzResearch.WordTrace]
  refine ⟨212252012834210087191533341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141501341889473391461022227 212252012834210087191533341)
  ·
    refine ⟨79594504812828782696825003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212252012834210087191533341 79594504812828782696825003)
    ·
      refine ⟨119391757219243174045237505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79594504812828782696825003 119391757219243174045237505)
      ·
        refine ⟨89543817914432380533928129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119391757219243174045237505 89543817914432380533928129)
        ·
          refine ⟨67157863435824285400446097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89543817914432380533928129 67157863435824285400446097)
          ·
            refine ⟨50368397576868214050334573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67157863435824285400446097 50368397576868214050334573)
            ·
              refine ⟨18888149091325580268875465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50368397576868214050334573 18888149091325580268875465)
              ·
                refine ⟨14166111818494185201656599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18888149091325580268875465 14166111818494185201656599)
                ·
                  refine ⟨21249167727741277802484899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14166111818494185201656599 21249167727741277802484899)
                  ·
                    refine ⟨31873751591611916703727349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21249167727741277802484899 31873751591611916703727349)
                    ·
                      refine ⟨2988164211713617190974439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31873751591611916703727349 2988164211713617190974439)
                      ·
                        rfl

theorem cell23_5819429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_5819429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819429 prefixEnd_5819429 := by exact prefixLift 5819429
  have htrace : WordTrace (prefixWord ++ tailWord_5819429) baseStart_5819429 baseEnd_5819429 := by
    simpa [prefixWord, tailWord_5819429, baseEnd_5819429] using wordTrace_append hprefix tailTrace_5819429
  have hstable : (prefixWord ++ tailWord_5819429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819429).length < 2 ^ (prefixWord ++ tailWord_5819429).sum := by decide
  have hdescent : baseEnd_5819429 < baseStart_5819429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819449 : List Nat := [1, 2, 1, 5, 2, 2, 1, 9]
def baseStart_5819449 : Nat := 118140960795 + 5819449 * 2 ^ 59
def prefixEnd_5819449 : Nat := 4983230072969 + 3 ^ 40 * 5819449 * 2
def baseEnd_5819449 : Nat := 110673128938026189360161

theorem tailTrace_5819449 : CollatzResearch.WordTrace tailWord_5819449 prefixEnd_5819449 110673128938026189360161 := by
  unfold tailWord_5819449
  simp only [CollatzResearch.WordTrace]
  refine ⟨212252742294137630607261401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141501828196091753738174267 212252742294137630607261401)
  ·
    refine ⟨159189556720603222955446051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212252742294137630607261401 159189556720603222955446051)
    ·
      refine ⟨238784335080904834433169077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159189556720603222955446051 238784335080904834433169077)
      ·
        refine ⟨22386031413834828228109601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238784335080904834433169077 22386031413834828228109601)
        ·
          refine ⟨16789523560376121171082201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22386031413834828228109601 16789523560376121171082201)
          ·
            refine ⟨12592142670282090878311651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16789523560376121171082201 12592142670282090878311651)
            ·
              refine ⟨18888214005423136317467477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12592142670282090878311651 18888214005423136317467477)
              ·
                refine ⟨110673128938026189360161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18888214005423136317467477 110673128938026189360161)
                ·
                  rfl

theorem cell23_5819449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 9].length) (baseStart_5819449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819449 prefixEnd_5819449 := by exact prefixLift 5819449
  have htrace : WordTrace (prefixWord ++ tailWord_5819449) baseStart_5819449 baseEnd_5819449 := by
    simpa [prefixWord, tailWord_5819449, baseEnd_5819449] using wordTrace_append hprefix tailTrace_5819449
  have hstable : (prefixWord ++ tailWord_5819449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819449).length < 2 ^ (prefixWord ++ tailWord_5819449).sum := by decide
  have hdescent : baseEnd_5819449 < baseStart_5819449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819459 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3]
def baseStart_5819459 : Nat := 118140960795 + 5819459 * 2 ^ 59
def prefixEnd_5819459 : Nat := 4983230072969 + 3 ^ 40 * 5819459 * 2
def baseEnd_5819459 : Nat := 2988179616133252073599301

theorem tailTrace_5819459 : CollatzResearch.WordTrace tailWord_5819459 prefixEnd_5819459 2988179616133252073599301 := by
  unfold tailWord_5819459
  simp only [CollatzResearch.WordTrace]
  refine ⟨212253107024101402315125431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141502071349400934876750287 212253107024101402315125431)
  ·
    refine ⟨318379660536152103472688147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212253107024101402315125431 318379660536152103472688147)
    ·
      refine ⟨477569490804228155209032221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318379660536152103472688147 477569490804228155209032221)
      ·
        refine ⟨179088559051585558203387083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477569490804228155209032221 179088559051585558203387083)
        ·
          refine ⟨268632838577378337305080625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179088559051585558203387083 268632838577378337305080625)
          ·
            refine ⟨201474628933033752978810469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268632838577378337305080625 201474628933033752978810469)
            ·
              refine ⟨37776492924943828683526963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201474628933033752978810469 37776492924943828683526963)
              ·
                refine ⟨56664739387415743025290445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37776492924943828683526963 56664739387415743025290445)
                ·
                  refine ⟨21249277270280903634483917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56664739387415743025290445 21249277270280903634483917)
                  ·
                    refine ⟨7968478976355338862931469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21249277270280903634483917 7968478976355338862931469)
                    ·
                      refine ⟨2988179616133252073599301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968478976355338862931469 2988179616133252073599301)
                      ·
                        rfl

theorem cell23_5819459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_5819459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819459 prefixEnd_5819459 := by exact prefixLift 5819459
  have htrace : WordTrace (prefixWord ++ tailWord_5819459) baseStart_5819459 baseEnd_5819459 := by
    simpa [prefixWord, tailWord_5819459, baseEnd_5819459] using wordTrace_append hprefix tailTrace_5819459
  have hstable : (prefixWord ++ tailWord_5819459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819459).length < 2 ^ (prefixWord ++ tailWord_5819459).sum := by decide
  have hdescent : baseEnd_5819459 < baseStart_5819459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819477 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5819477 : Nat := 118140960795 + 5819477 * 2 ^ 59
def prefixEnd_5819477 : Nat := 4983230072969 + 3 ^ 40 * 5819477 * 2
def baseEnd_5819477 : Nat := 2988188858785033003174219

theorem tailTrace_5819477 : CollatzResearch.WordTrace tailWord_5819477 prefixEnd_5819477 2988188858785033003174219 := by
  unfold tailWord_5819477
  simp only [CollatzResearch.WordTrace]
  refine ⟨212253763538036191389280685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141502509025357460926187123 212253763538036191389280685)
  ·
    refine ⟨79595161326763571770980257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212253763538036191389280685 79595161326763571770980257)
    ·
      refine ⟨59696370995072678828235193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79595161326763571770980257 59696370995072678828235193)
      ·
        refine ⟨44772278246304509121176395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59696370995072678828235193 44772278246304509121176395)
        ·
          refine ⟨67158417369456763681764593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44772278246304509121176395 67158417369456763681764593)
          ·
            refine ⟨50368813027092572761323445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67158417369456763681764593 50368813027092572761323445)
            ·
              refine ⟨4722076221289928696374073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50368813027092572761323445 4722076221289928696374073)
              ·
                refine ⟨3541557165967446522280555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4722076221289928696374073 3541557165967446522280555)
                ·
                  refine ⟨5312335748951169783420833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541557165967446522280555 5312335748951169783420833)
                  ·
                    refine ⟨3984251811713377337565625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312335748951169783420833 3984251811713377337565625)
                    ·
                      refine ⟨2988188858785033003174219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984251811713377337565625 2988188858785033003174219)
                      ·
                        rfl

theorem cell23_5819477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5819477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819477 prefixEnd_5819477 := by exact prefixLift 5819477
  have htrace : WordTrace (prefixWord ++ tailWord_5819477) baseStart_5819477 baseEnd_5819477 := by
    simpa [prefixWord, tailWord_5819477, baseEnd_5819477] using wordTrace_append hprefix tailTrace_5819477
  have hstable : (prefixWord ++ tailWord_5819477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819477).length < 2 ^ (prefixWord ++ tailWord_5819477).sum := by decide
  have hdescent : baseEnd_5819477 < baseStart_5819477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819493 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_5819493 : Nat := 118140960795 + 5819493 * 2 ^ 59
def prefixEnd_5819493 : Nat := 4983230072969 + 3 ^ 40 * 5819493 * 2
def baseEnd_5819493 : Nat := 2988197074475504940574145

theorem tailTrace_5819493 : CollatzResearch.WordTrace tailWord_5819493 prefixEnd_5819493 2988197074475504940574145 := by
  unfold tailWord_5819493
  simp only [CollatzResearch.WordTrace]
  refine ⟨212254347105978226121863133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141502898070652150747908755 212254347105978226121863133)
  ·
    refine ⟨79595380164741834795698675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212254347105978226121863133 79595380164741834795698675)
    ·
      refine ⟨119393070247112752193548013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79595380164741834795698675 119393070247112752193548013)
      ·
        refine ⟨44772401342667282072580505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119393070247112752193548013 44772401342667282072580505)
        ·
          refine ⟨33579301007000461554435379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44772401342667282072580505 33579301007000461554435379)
          ·
            refine ⟨50368951510500692331653069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33579301007000461554435379 50368951510500692331653069)
            ·
              refine ⟨18888356816437759624369901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50368951510500692331653069 18888356816437759624369901)
              ·
                refine ⟨7083133806164159859138713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18888356816437759624369901 7083133806164159859138713)
                ·
                  refine ⟨5312350354623119894354035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083133806164159859138713 5312350354623119894354035)
                  ·
                    refine ⟨7968525531934679841531053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312350354623119894354035 7968525531934679841531053)
                    ·
                      refine ⟨2988197074475504940574145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968525531934679841531053 2988197074475504940574145)
                      ·
                        rfl

theorem cell23_5819493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_5819493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819493 prefixEnd_5819493 := by exact prefixLift 5819493
  have htrace : WordTrace (prefixWord ++ tailWord_5819493) baseStart_5819493 baseEnd_5819493 := by
    simpa [prefixWord, tailWord_5819493, baseEnd_5819493] using wordTrace_append hprefix tailTrace_5819493
  have hstable : (prefixWord ++ tailWord_5819493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819493).length < 2 ^ (prefixWord ++ tailWord_5819493).sum := by decide
  have hdescent : baseEnd_5819493 < baseStart_5819493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819519 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_5819519 : Nat := 118140960795 + 5819519 * 2 ^ 59
def prefixEnd_5819519 : Nat := 4983230072969 + 3 ^ 40 * 5819519 * 2
def baseEnd_5819519 : Nat := 2988210424972521838849025

theorem tailTrace_5819519 : CollatzResearch.WordTrace tailWord_5819519 prefixEnd_5819519 2988210424972521838849025 := by
  unfold tailWord_5819519
  simp only [CollatzResearch.WordTrace]
  refine ⟨212255295403884032562309611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141503530269256021708206407 212255295403884032562309611)
  ·
    refine ⟨318382943105826048843464417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212255295403884032562309611 318382943105826048843464417)
    ·
      refine ⟨238787207329369536632598313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318382943105826048843464417 238787207329369536632598313)
      ·
        refine ⟨179090405497027152474448735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238787207329369536632598313 179090405497027152474448735)
        ·
          refine ⟨268635608245540728711673103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179090405497027152474448735 268635608245540728711673103)
          ·
            refine ⟨402953412368311093067509655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268635608245540728711673103 402953412368311093067509655)
            ·
              refine ⟨604430118552466639601264483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402953412368311093067509655 604430118552466639601264483)
              ·
                refine ⟨906645177828699959401896725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604430118552466639601264483 906645177828699959401896725)
                ·
                  refine ⟨42498992710720310596963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 906645177828699959401896725 42498992710720310596963909)
                  ·
                    refine ⟨7968561133260058236930733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42498992710720310596963909 7968561133260058236930733)
                    ·
                      refine ⟨2988210424972521838849025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968561133260058236930733 2988210424972521838849025)
                      ·
                        rfl

theorem cell23_5819519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_5819519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819519 prefixEnd_5819519 := by exact prefixLift 5819519
  have htrace : WordTrace (prefixWord ++ tailWord_5819519) baseStart_5819519 baseEnd_5819519 := by
    simpa [prefixWord, tailWord_5819519, baseEnd_5819519] using wordTrace_append hprefix tailTrace_5819519
  have hstable : (prefixWord ++ tailWord_5819519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819519).length < 2 ^ (prefixWord ++ tailWord_5819519).sum := by decide
  have hdescent : baseEnd_5819519 < baseStart_5819519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819546 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5819546 : Nat := 118140960795 + 5819546 * 2 ^ 59
def prefixEnd_5819546 : Nat := 4983230072969 + 3 ^ 40 * 5819546 * 2
def baseEnd_5819546 : Nat := 2988224288950193233211401

theorem tailTrace_5819546 : CollatzResearch.WordTrace tailWord_5819546 prefixEnd_5819546 2988224288950193233211401 := by
  unfold tailWord_5819546
  simp only [CollatzResearch.WordTrace]
  refine ⟨53064070043696554043385623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141504186783190810782361661 53064070043696554043385623)
  ·
    refine ⟨79596105065544831065078435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53064070043696554043385623 79596105065544831065078435)
    ·
      refine ⟨119394157598317246597617653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79596105065544831065078435 119394157598317246597617653)
      ·
        refine ⟨11193202274842241868526655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119394157598317246597617653 11193202274842241868526655)
        ·
          refine ⟨16789803412263362802789983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193202274842241868526655 16789803412263362802789983)
          ·
            refine ⟨25184705118395044204184975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16789803412263362802789983 25184705118395044204184975)
            ·
              refine ⟨37777057677592566306277463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25184705118395044204184975 37777057677592566306277463)
              ·
                refine ⟨56665586516388849459416195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37777057677592566306277463 56665586516388849459416195)
                ·
                  refine ⟨84998379774583274189124293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56665586516388849459416195 84998379774583274189124293)
                  ·
                    refine ⟨15937196207734363910460805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84998379774583274189124293 15937196207734363910460805)
                    ·
                      refine ⟨2988224288950193233211401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15937196207734363910460805 2988224288950193233211401)
                      ·
                        rfl

theorem cell23_5819546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5819546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819546 prefixEnd_5819546 := by exact prefixLift 5819546
  have htrace : WordTrace (prefixWord ++ tailWord_5819546) baseStart_5819546 baseEnd_5819546 := by
    simpa [prefixWord, tailWord_5819546, baseEnd_5819546] using wordTrace_append hprefix tailTrace_5819546
  have hstable : (prefixWord ++ tailWord_5819546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819546).length < 2 ^ (prefixWord ++ tailWord_5819546).sum := by decide
  have hdescent : baseEnd_5819546 < baseStart_5819546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819550 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5819550 : Nat := 118140960795 + 5819550 * 2 ^ 59
def prefixEnd_5819550 : Nat := 4983230072969 + 3 ^ 40 * 5819550 * 2
def baseEnd_5819550 : Nat := 2988226342872811217561383

theorem tailTrace_5819550 : CollatzResearch.WordTrace tailWord_5819550 prefixEnd_5819550 2988226342872811217561383 := by
  unfold tailWord_5819550
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532053258346465607086013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141504284044514483237792069 26532053258346465607086013)
  ·
    refine ⟨9949519971879924602657255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26532053258346465607086013 9949519971879924602657255)
    ·
      refine ⟨14924279957819886903985883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9949519971879924602657255 14924279957819886903985883)
      ·
        refine ⟨22386419936729830355978825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14924279957819886903985883 22386419936729830355978825)
        ·
          refine ⟨16789814952547372766984119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22386419936729830355978825 16789814952547372766984119)
          ·
            refine ⟨25184722428821059150476179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16789814952547372766984119 25184722428821059150476179)
            ·
              refine ⟨37777083643231588725714269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25184722428821059150476179 37777083643231588725714269)
              ·
                refine ⟨14166406366211845772142851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37777083643231588725714269 14166406366211845772142851)
                ·
                  refine ⟨21249609549317768658214277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14166406366211845772142851 21249609549317768658214277)
                  ·
                    refine ⟨3984301790497081623415177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21249609549317768658214277 3984301790497081623415177)
                    ·
                      refine ⟨2988226342872811217561383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984301790497081623415177 2988226342872811217561383)
                      ·
                        rfl

theorem cell23_5819550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5819550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819550 prefixEnd_5819550 := by exact prefixLift 5819550
  have htrace : WordTrace (prefixWord ++ tailWord_5819550) baseStart_5819550 baseEnd_5819550 := by
    simpa [prefixWord, tailWord_5819550, baseEnd_5819550] using wordTrace_append hprefix tailTrace_5819550
  have hstable : (prefixWord ++ tailWord_5819550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819550).length < 2 ^ (prefixWord ++ tailWord_5819550).sum := by decide
  have hdescent : baseEnd_5819550 < baseStart_5819550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819556 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 7]
def baseStart_5819556 : Nat := 118140960795 + 5819556 * 2 ^ 59
def prefixEnd_5819556 : Nat := 4983230072969 + 3 ^ 40 * 5819556 * 2
def baseEnd_5819556 : Nat := 332025491528526466009595

theorem tailTrace_5819556 : CollatzResearch.WordTrace tailWord_5819556 prefixEnd_5819556 332025491528526466009595 := by
  unfold tailWord_5819556
  simp only [CollatzResearch.WordTrace]
  refine ⟨106128322452374993940703261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141504429936499991920937681 106128322452374993940703261)
  ·
    refine ⟨39798120919640622727763723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106128322452374993940703261 39798120919640622727763723)
    ·
      refine ⟨59697181379460934091645585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39798120919640622727763723 59697181379460934091645585)
      ·
        refine ⟨44772886034595700568734189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59697181379460934091645585 44772886034595700568734189)
        ·
          refine ⟨16789832262973387713275321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44772886034595700568734189 16789832262973387713275321)
          ·
            refine ⟨12592374197230040784956491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16789832262973387713275321 12592374197230040784956491)
            ·
              refine ⟨18888561295845061177434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12592374197230040784956491 18888561295845061177434737)
              ·
                refine ⟨14166420971883795883076053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18888561295845061177434737 14166420971883795883076053)
                ·
                  refine ⟨332025491528526466009595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14166420971883795883076053 332025491528526466009595)
                  ·
                    rfl

theorem cell23_5819556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_5819556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819556 prefixEnd_5819556 := by exact prefixLift 5819556
  have htrace : WordTrace (prefixWord ++ tailWord_5819556) baseStart_5819556 baseEnd_5819556 := by
    simpa [prefixWord, tailWord_5819556, baseEnd_5819556] using wordTrace_append hprefix tailTrace_5819556
  have hstable : (prefixWord ++ tailWord_5819556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819556).length < 2 ^ (prefixWord ++ tailWord_5819556).sum := by decide
  have hdescent : baseEnd_5819556 < baseStart_5819556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819576 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_5819576 : Nat := 118140960795 + 5819576 * 2 ^ 59
def prefixEnd_5819576 : Nat := 4983230072969 + 3 ^ 40 * 5819576 * 2
def baseEnd_5819576 : Nat := 2988239693369828115836263

theorem tailTrace_5819576 : CollatzResearch.WordTrace tailWord_5819576 prefixEnd_5819576 2988239693369828115836263 := by
  unfold tailWord_5819576
  simp only [CollatzResearch.WordTrace]
  refine ⟨106128687182338765648567291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141504916243118354198089721 106128687182338765648567291)
  ·
    refine ⟨159193030773508148472850937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106128687182338765648567291 159193030773508148472850937)
    ·
      refine ⟨119394773080131111354638203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159193030773508148472850937 119394773080131111354638203)
      ·
        refine ⟨179092159620196667031957305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119394773080131111354638203 179092159620196667031957305)
        ·
          refine ⟨134319119715147500273967979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179092159620196667031957305 134319119715147500273967979)
          ·
            refine ⟨201478679572721250410951969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134319119715147500273967979 201478679572721250410951969)
            ·
              refine ⟨151109009679540937808213977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201478679572721250410951969 151109009679540937808213977)
              ·
                refine ⟨113331757259655703356160483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151109009679540937808213977 113331757259655703356160483)
                ·
                  refine ⟨169997635889483555034240725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113331757259655703356160483 169997635889483555034240725)
                  ·
                    refine ⟨3984319591159770821115017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169997635889483555034240725 3984319591159770821115017)
                    ·
                      refine ⟨2988239693369828115836263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984319591159770821115017 2988239693369828115836263)
                      ·
                        rfl

theorem cell23_5819576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_5819576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819576 prefixEnd_5819576 := by exact prefixLift 5819576
  have htrace : WordTrace (prefixWord ++ tailWord_5819576) baseStart_5819576 baseEnd_5819576 := by
    simpa [prefixWord, tailWord_5819576, baseEnd_5819576] using wordTrace_append hprefix tailTrace_5819576
  have hstable : (prefixWord ++ tailWord_5819576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819576).length < 2 ^ (prefixWord ++ tailWord_5819576).sum := by decide
  have hdescent : baseEnd_5819576 < baseStart_5819576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819579 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_5819579 : Nat := 118140960795 + 5819579 * 2 ^ 59
def prefixEnd_5819579 : Nat := 4983230072969 + 3 ^ 40 * 5819579 * 2
def baseEnd_5819579 : Nat := 2988241233811791604098749

theorem tailTrace_5819579 : CollatzResearch.WordTrace tailWord_5819579 prefixEnd_5819579 2988241233811791604098749 := by
  unfold tailWord_5819579
  simp only [CollatzResearch.WordTrace]
  refine ⟨212257483783666662809493791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141504989189111108539662527 212257483783666662809493791)
  ·
    refine ⟨318386225675499994214240687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212257483783666662809493791 318386225675499994214240687)
    ·
      refine ⟨477579338513249991321361031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318386225675499994214240687 477579338513249991321361031)
      ·
        refine ⟨716369007769874986982041547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477579338513249991321361031 716369007769874986982041547)
        ·
          refine ⟨1074553511654812480473062321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716369007769874986982041547 1074553511654812480473062321)
          ·
            refine ⟨805915133741109360354796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074553511654812480473062321 805915133741109360354796741)
            ·
              refine ⟨151109087576458005066524389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 805915133741109360354796741 151109087576458005066524389)
              ·
                refine ⟨28332953920585875949973323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151109087576458005066524389 28332953920585875949973323)
                ·
                  refine ⟨42499430880878813924959985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28332953920585875949973323 42499430880878813924959985)
                  ·
                    refine ⟨31874573160659110443719989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42499430880878813924959985 31874573160659110443719989)
                    ·
                      refine ⟨2988241233811791604098749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31874573160659110443719989 2988241233811791604098749)
                      ·
                        rfl

theorem cell23_5819579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_5819579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819579 prefixEnd_5819579 := by exact prefixLift 5819579
  have htrace : WordTrace (prefixWord ++ tailWord_5819579) baseStart_5819579 baseEnd_5819579 := by
    simpa [prefixWord, tailWord_5819579, baseEnd_5819579] using wordTrace_append hprefix tailTrace_5819579
  have hstable : (prefixWord ++ tailWord_5819579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819579).length < 2 ^ (prefixWord ++ tailWord_5819579).sum := by decide
  have hdescent : baseEnd_5819579 < baseStart_5819579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819584 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2]
def baseStart_5819584 : Nat := 118140960795 + 5819584 * 2 ^ 59
def prefixEnd_5819584 : Nat := 4983230072969 + 3 ^ 40 * 5819584 * 2
def baseEnd_5819584 : Nat := 2988243801215064084536227

theorem tailTrace_5819584 : CollatzResearch.WordTrace tailWord_5819584 prefixEnd_5819584 2988243801215064084536227 := by
  unfold tailWord_5819584
  simp only [CollatzResearch.WordTrace]
  refine ⟨106128833074324274331712903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141505110765765699108950537 106128833074324274331712903)
  ·
    refine ⟨159193249611486411497569355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106128833074324274331712903 159193249611486411497569355)
    ·
      refine ⟨238789874417229617246354033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159193249611486411497569355 238789874417229617246354033)
      ·
        refine ⟨179092405812922212934765525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238789874417229617246354033 179092405812922212934765525)
        ·
          refine ⟨4197478261240364365658567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 179092405812922212934765525 4197478261240364365658567)
          ·
            refine ⟨6296217391860546548487851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197478261240364365658567 6296217391860546548487851)
            ·
              refine ⟨9444326087790819822731777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296217391860546548487851 9444326087790819822731777)
              ·
                refine ⟨7083244565843114867048833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444326087790819822731777 7083244565843114867048833)
                ·
                  refine ⟨5312433424382336150286625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083244565843114867048833 5312433424382336150286625)
                  ·
                    refine ⟨3984325068286752112714969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312433424382336150286625 3984325068286752112714969)
                    ·
                      refine ⟨2988243801215064084536227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984325068286752112714969 2988243801215064084536227)
                      ·
                        rfl

theorem cell23_5819584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_5819584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819584 prefixEnd_5819584 := by exact prefixLift 5819584
  have htrace : WordTrace (prefixWord ++ tailWord_5819584) baseStart_5819584 baseEnd_5819584 := by
    simpa [prefixWord, tailWord_5819584, baseEnd_5819584] using wordTrace_append hprefix tailTrace_5819584
  have hstable : (prefixWord ++ tailWord_5819584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819584).length < 2 ^ (prefixWord ++ tailWord_5819584).sum := by decide
  have hdescent : baseEnd_5819584 < baseStart_5819584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819706 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_5819706 : Nat := 118140960795 + 5819706 * 2 ^ 59
def prefixEnd_5819706 : Nat := 4983230072969 + 3 ^ 40 * 5819706 * 2
def baseEnd_5819706 : Nat := 996102148618304202403555

theorem tailTrace_5819706 : CollatzResearch.WordTrace tailWord_5819706 prefixEnd_5819706 996102148618304202403555 := by
  unfold tailWord_5819706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065528963551640874841743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141508077236137708999577981 53065528963551640874841743)
  ·
    refine ⟨79598293445327461312262615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53065528963551640874841743 79598293445327461312262615)
    ·
      refine ⟨119397440167991191968393923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79598293445327461312262615 119397440167991191968393923)
      ·
        refine ⟨179096160251986787952590885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119397440167991191968393923 179096160251986787952590885)
        ·
          refine ⟨33580530047247522741110791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179096160251986787952590885 33580530047247522741110791)
          ·
            refine ⟨50370795070871284111666187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33580530047247522741110791 50370795070871284111666187)
            ·
              refine ⟨75556192606306926167499281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50370795070871284111666187 75556192606306926167499281)
              ·
                refine ⟨56667144454730194625624461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75556192606306926167499281 56667144454730194625624461)
                ·
                  refine ⟨21250179170523822984609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56667144454730194625624461 21250179170523822984609173)
                  ·
                    refine ⟨996102148618304202403555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21250179170523822984609173 996102148618304202403555)
                    ·
                      rfl

theorem cell23_5819706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_5819706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819706 prefixEnd_5819706 := by exact prefixLift 5819706
  have htrace : WordTrace (prefixWord ++ tailWord_5819706) baseStart_5819706 baseEnd_5819706 := by
    simpa [prefixWord, tailWord_5819706, baseEnd_5819706] using wordTrace_append hprefix tailTrace_5819706
  have hstable : (prefixWord ++ tailWord_5819706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819706).length < 2 ^ (prefixWord ++ tailWord_5819706).sum := by decide
  have hdescent : baseEnd_5819706 < baseStart_5819706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819747 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5819747 : Nat := 118140960795 + 5819747 * 2 ^ 59
def prefixEnd_5819747 : Nat := 4983230072969 + 3 ^ 40 * 5819747 * 2
def baseEnd_5819747 : Nat := 2988327498561746946797977

theorem tailTrace_5819747 : CollatzResearch.WordTrace tailWord_5819747 prefixEnd_5819747 2988327498561746946797977 := by
  unfold tailWord_5819747
  simp only [CollatzResearch.WordTrace]
  refine ⟨212263611247058027501609495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141509074164705351667739663 212263611247058027501609495)
  ·
    refine ⟨318395416870587041252414243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212263611247058027501609495 318395416870587041252414243)
    ·
      refine ⟨477593125305880561878621365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318395416870587041252414243 477593125305880561878621365)
      ·
        refine ⟨44774355497426302676120753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 477593125305880561878621365 44774355497426302676120753)
        ·
          refine ⟨33580766623069727007090565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44774355497426302676120753 33580766623069727007090565)
          ·
            refine ⟨6296393741825573813829481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33580766623069727007090565 6296393741825573813829481)
            ·
              refine ⟨4722295306369180360372111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6296393741825573813829481 4722295306369180360372111)
              ·
                refine ⟨7083442959553770540558167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722295306369180360372111 7083442959553770540558167)
                ·
                  refine ⟨10625164439330655810837251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083442959553770540558167 10625164439330655810837251)
                  ·
                    refine ⟨15937746658995983716255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10625164439330655810837251 15937746658995983716255877)
                    ·
                      refine ⟨2988327498561746946797977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15937746658995983716255877 2988327498561746946797977)
                      ·
                        rfl

theorem cell23_5819747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5819747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819747 prefixEnd_5819747 := by exact prefixLift 5819747
  have htrace : WordTrace (prefixWord ++ tailWord_5819747) baseStart_5819747 baseEnd_5819747 := by
    simpa [prefixWord, tailWord_5819747, baseEnd_5819747] using wordTrace_append hprefix tailTrace_5819747
  have hstable : (prefixWord ++ tailWord_5819747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819747).length < 2 ^ (prefixWord ++ tailWord_5819747).sum := by decide
  have hdescent : baseEnd_5819747 < baseStart_5819747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819757 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_5819757 : Nat := 118140960795 + 5819757 * 2 ^ 59
def prefixEnd_5819757 : Nat := 4983230072969 + 3 ^ 40 * 5819757 * 2
def baseEnd_5819757 : Nat := 996110877789430635890977

theorem tailTrace_5819757 : CollatzResearch.WordTrace tailWord_5819757 prefixEnd_5819757 996110877789430635890977 := by
  unfold tailWord_5819757
  simp only [CollatzResearch.WordTrace]
  refine ⟨212263975977021799209473525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141509317318014532806315683 212263975977021799209473525)
  ·
    refine ⟨19899747747845793675888143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212263975977021799209473525 19899747747845793675888143)
    ·
      refine ⟨29849621621768690513832215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19899747747845793675888143 29849621621768690513832215)
      ·
        refine ⟨44774432432653035770748323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29849621621768690513832215 44774432432653035770748323)
        ·
          refine ⟨67161648648979553656122485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44774432432653035770748323 67161648648979553656122485)
          ·
            refine ⟨6296404560841833155261483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67161648648979553656122485 6296404560841833155261483)
            ·
              refine ⟨9444606841262749732892225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296404560841833155261483 9444606841262749732892225)
              ·
                refine ⟨7083455130947062299669169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444606841262749732892225 7083455130947062299669169)
                ·
                  refine ⟨5312591348210296724751877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083455130947062299669169 5312591348210296724751877)
                  ·
                    refine ⟨996110877789430635890977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5312591348210296724751877 996110877789430635890977)
                    ·
                      rfl

theorem cell23_5819757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_5819757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819757 prefixEnd_5819757 := by exact prefixLift 5819757
  have htrace : WordTrace (prefixWord ++ tailWord_5819757) baseStart_5819757 baseEnd_5819757 := by
    simpa [prefixWord, tailWord_5819757, baseEnd_5819757] using wordTrace_append hprefix tailTrace_5819757
  have hstable : (prefixWord ++ tailWord_5819757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819757).length < 2 ^ (prefixWord ++ tailWord_5819757).sum := by decide
  have hdescent : baseEnd_5819757 < baseStart_5819757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819774 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5819774 : Nat := 118140960795 + 5819774 * 2 ^ 59
def prefixEnd_5819774 : Nat := 4983230072969 + 3 ^ 40 * 5819774 * 2
def baseEnd_5819774 : Nat := 996113787513139447053451

theorem tailTrace_5819774 : CollatzResearch.WordTrace tailWord_5819774 prefixEnd_5819774 996113787513139447053451 := by
  unfold tailWord_5819774
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533074502245026389105297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141509730678640140741894917 26533074502245026389105297)
  ·
    refine ⟨19899805876683769791828973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26533074502245026389105297 19899805876683769791828973)
    ·
      refine ⟨7462427203756413671935865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19899805876683769791828973 7462427203756413671935865)
      ·
        refine ⟨5596820402817310253951899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7462427203756413671935865 5596820402817310253951899)
        ·
          refine ⟨8395230604225965380927849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596820402817310253951899 8395230604225965380927849)
          ·
            refine ⟨6296422953169474035695887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8395230604225965380927849 6296422953169474035695887)
            ·
              refine ⟨9444634429754211053543831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296422953169474035695887 9444634429754211053543831)
              ·
                refine ⟨14166951644631316580315747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444634429754211053543831 14166951644631316580315747)
                ·
                  refine ⟨21250427466946974870473621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14166951644631316580315747 21250427466946974870473621)
                  ·
                    refine ⟨996113787513139447053451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21250427466946974870473621 996113787513139447053451)
                    ·
                      rfl

theorem cell23_5819774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5819774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819774 prefixEnd_5819774 := by exact prefixLift 5819774
  have htrace : WordTrace (prefixWord ++ tailWord_5819774) baseStart_5819774 baseEnd_5819774 := by
    simpa [prefixWord, tailWord_5819774, baseEnd_5819774] using wordTrace_append hprefix tailTrace_5819774
  have hstable : (prefixWord ++ tailWord_5819774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819774).length < 2 ^ (prefixWord ++ tailWord_5819774).sum := by decide
  have hdescent : baseEnd_5819774 < baseStart_5819774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819776 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_5819776 : Nat := 118140960795 + 5819776 * 2 ^ 59
def prefixEnd_5819776 : Nat := 4983230072969 + 3 ^ 40 * 5819776 * 2
def baseEnd_5819776 : Nat := 2988342389500727333335343

theorem tailTrace_5819776 : CollatzResearch.WordTrace tailWord_5819776 prefixEnd_5819776 2988342389500727333335343 := by
  unfold tailWord_5819776
  simp only [CollatzResearch.WordTrace]
  refine ⟨106132334481976482727207591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141509779309301976969610121 106132334481976482727207591)
  ·
    refine ⟨159198501722964724090811387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106132334481976482727207591 159198501722964724090811387)
    ·
      refine ⟨238797752584447086136217081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159198501722964724090811387 238797752584447086136217081)
      ·
        refine ⟨179098314438335314602162811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238797752584447086136217081 179098314438335314602162811)
        ·
          refine ⟨268647471657502971903244217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179098314438335314602162811 268647471657502971903244217)
          ·
            refine ⟨201485603743127228927433163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268647471657502971903244217 201485603743127228927433163)
            ·
              refine ⟨302228405614690843391149745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201485603743127228927433163 302228405614690843391149745)
              ·
                refine ⟨226671304211018132543362309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302228405614690843391149745 226671304211018132543362309)
                ·
                  refine ⟨42500869539565899851880433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226671304211018132543362309 42500869539565899851880433)
                  ·
                    refine ⟨31875652154674424888910325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42500869539565899851880433 31875652154674424888910325)
                    ·
                      refine ⟨2988342389500727333335343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31875652154674424888910325 2988342389500727333335343)
                      ·
                        rfl

theorem cell23_5819776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_5819776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819776 prefixEnd_5819776 := by exact prefixLift 5819776
  have htrace : WordTrace (prefixWord ++ tailWord_5819776) baseStart_5819776 baseEnd_5819776 := by
    simpa [prefixWord, tailWord_5819776, baseEnd_5819776] using wordTrace_append hprefix tailTrace_5819776
  have hstable : (prefixWord ++ tailWord_5819776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819776).length < 2 ^ (prefixWord ++ tailWord_5819776).sum := by decide
  have hdescent : baseEnd_5819776 < baseStart_5819776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819777 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5819777 : Nat := 118140960795 + 5819777 * 2 ^ 59
def prefixEnd_5819777 : Nat := 4983230072969 + 3 ^ 40 * 5819777 * 2
def baseEnd_5819777 : Nat := 2988342902981381829422839

theorem tailTrace_5819777 : CollatzResearch.WordTrace tailWord_5819777 prefixEnd_5819777 2988342902981381829422839 := by
  unfold tailWord_5819777
  simp only [CollatzResearch.WordTrace]
  refine ⟨212264705436949342625201585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141509803624632895083467723 212264705436949342625201585)
  ·
    refine ⟨159198529077712006968901189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212264705436949342625201585 159198529077712006968901189)
    ·
      refine ⟨29849724202071001306668973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159198529077712006968901189 29849724202071001306668973)
      ·
        refine ⟨11193646575776625490000865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29849724202071001306668973 11193646575776625490000865)
        ·
          refine ⟨8395234931832469117500649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11193646575776625490000865 8395234931832469117500649)
          ·
            refine ⟨6296426198874351838125487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8395234931832469117500649 6296426198874351838125487)
            ·
              refine ⟨9444639298311527757188231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296426198874351838125487 9444639298311527757188231)
              ·
                refine ⟨14166958947467291635782347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444639298311527757188231 14166958947467291635782347)
                ·
                  refine ⟨21250438421200937453673521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14166958947467291635782347 21250438421200937453673521)
                  ·
                    refine ⟨15937828815900703090255141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21250438421200937453673521 15937828815900703090255141)
                    ·
                      refine ⟨2988342902981381829422839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15937828815900703090255141 2988342902981381829422839)
                      ·
                        rfl

theorem cell23_5819777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5819777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819777 prefixEnd_5819777 := by exact prefixLift 5819777
  have htrace : WordTrace (prefixWord ++ tailWord_5819777) baseStart_5819777 baseEnd_5819777 := by
    simpa [prefixWord, tailWord_5819777, baseEnd_5819777] using wordTrace_append hprefix tailTrace_5819777
  have hstable : (prefixWord ++ tailWord_5819777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819777).length < 2 ^ (prefixWord ++ tailWord_5819777).sum := by decide
  have hdescent : baseEnd_5819777 < baseStart_5819777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819780 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5819780 : Nat := 118140960795 + 5819780 * 2 ^ 59
def prefixEnd_5819780 : Nat := 4983230072969 + 3 ^ 40 * 5819780 * 2
def baseEnd_5819780 : Nat := 2988344443423345317685325

theorem tailTrace_5819780 : CollatzResearch.WordTrace tailWord_5819780 prefixEnd_5819780 2988344443423345317685325 := by
  unfold tailWord_5819780
  simp only [CollatzResearch.WordTrace]
  refine ⟨106132407427969237068780397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141509876570625649425040529 106132407427969237068780397)
  ·
    refine ⟨39799652785488463900792649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106132407427969237068780397 39799652785488463900792649)
    ·
      refine ⟨29849739589116347925594487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39799652785488463900792649 29849739589116347925594487)
      ·
        refine ⟨44774609383674521888391731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29849739589116347925594487 44774609383674521888391731)
        ·
          refine ⟨67161914075511782832587597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44774609383674521888391731 67161914075511782832587597)
          ·
            refine ⟨25185717778316918562220349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67161914075511782832587597 25185717778316918562220349)
            ·
              refine ⟨9444644166868844460832631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25185717778316918562220349 9444644166868844460832631)
              ·
                refine ⟨14166966250303266691248947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444644166868844460832631 14166966250303266691248947)
                ·
                  refine ⟨21250449375454900036873421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14166966250303266691248947 21250449375454900036873421)
                  ·
                    refine ⟨7968918515795587513827533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21250449375454900036873421 7968918515795587513827533)
                    ·
                      refine ⟨2988344443423345317685325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7968918515795587513827533 2988344443423345317685325)
                      ·
                        rfl

theorem cell23_5819780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5819780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819780 prefixEnd_5819780 := by exact prefixLift 5819780
  have htrace : WordTrace (prefixWord ++ tailWord_5819780) baseStart_5819780 baseEnd_5819780 := by
    simpa [prefixWord, tailWord_5819780, baseEnd_5819780] using wordTrace_append hprefix tailTrace_5819780
  have hstable : (prefixWord ++ tailWord_5819780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819780).length < 2 ^ (prefixWord ++ tailWord_5819780).sum := by decide
  have hdescent : baseEnd_5819780 < baseStart_5819780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 8, 2]
def baseStart_5819803 : Nat := 118140960795 + 5819803 * 2 ^ 59
def prefixEnd_5819803 : Nat := 4983230072969 + 3 ^ 40 * 5819803 * 2
def baseEnd_5819803 : Nat := 2988356253478398727697719

theorem tailTrace_5819803 : CollatzResearch.WordTrace tailWord_5819803 prefixEnd_5819803 2988356253478398727697719 := by
  unfold tailWord_5819803
  simp only [CollatzResearch.WordTrace]
  refine ⟨212265653734855149065648063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141510435823236766043765375 212265653734855149065648063)
  ·
    refine ⟨318398480602282723598472095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212265653734855149065648063 318398480602282723598472095)
    ·
      refine ⟨477597720903424085397708143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318398480602282723598472095 477597720903424085397708143)
      ·
        refine ⟨716396581355136128096562215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477597720903424085397708143 716396581355136128096562215)
        ·
          refine ⟨1074594872032704192144843323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716396581355136128096562215 1074594872032704192144843323)
          ·
            refine ⟨1611892308049056288217264985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074594872032704192144843323 1611892308049056288217264985)
            ·
              refine ⟨1208919231036792216162948739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611892308049056288217264985 1208919231036792216162948739)
              ·
                refine ⟨1813378846555188324244423109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208919231036792216162948739 1813378846555188324244423109)
                ·
                  refine ⟨340008533729097810795829333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813378846555188324244423109 340008533729097810795829333)
                  ·
                    refine ⟨3984475004637864970263625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 340008533729097810795829333 3984475004637864970263625)
                    ·
                      refine ⟨2988356253478398727697719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984475004637864970263625 2988356253478398727697719)
                      ·
                        rfl

theorem cell23_5819803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8, 2].length) (baseStart_5819803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819803 prefixEnd_5819803 := by exact prefixLift 5819803
  have htrace : WordTrace (prefixWord ++ tailWord_5819803) baseStart_5819803 baseEnd_5819803 := by
    simpa [prefixWord, tailWord_5819803, baseEnd_5819803] using wordTrace_append hprefix tailTrace_5819803
  have hstable : (prefixWord ++ tailWord_5819803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819803).length < 2 ^ (prefixWord ++ tailWord_5819803).sum := by decide
  have hdescent : baseEnd_5819803 < baseStart_5819803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819807 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 1, 3, 2]
def baseStart_5819807 : Nat := 118140960795 + 5819807 * 2 ^ 59
def prefixEnd_5819807 : Nat := 4983230072969 + 3 ^ 40 * 5819807 * 2
def baseEnd_5819807 : Nat := 2988358307401016712047701

theorem tailTrace_5819807 : CollatzResearch.WordTrace tailWord_5819807 prefixEnd_5819807 2988358307401016712047701 := by
  unfold tailWord_5819807
  simp only [CollatzResearch.WordTrace]
  refine ⟨212265799626840657748793675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141510533084560438499195783 212265799626840657748793675)
  ·
    refine ⟨318398699440260986623190513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212265799626840657748793675 318398699440260986623190513)
    ·
      refine ⟨238799024580195739967392885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318398699440260986623190513 238799024580195739967392885)
      ·
        refine ⟨22387408554393350621943083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238799024580195739967392885 22387408554393350621943083)
        ·
          refine ⟨33581112831590025932914625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22387408554393350621943083 33581112831590025932914625)
          ·
            refine ⟨25185834623692519449685969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33581112831590025932914625 25185834623692519449685969)
            ·
              refine ⟨18889375967769389587264477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25185834623692519449685969 18889375967769389587264477)
              ·
                refine ⟨7083515987913521095224179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18889375967769389587264477 7083515987913521095224179)
                ·
                  refine ⟨10625273981870281642836269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083515987913521095224179 10625273981870281642836269)
                  ·
                    refine ⟨3984477743201355616063601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10625273981870281642836269 3984477743201355616063601)
                    ·
                      refine ⟨2988358307401016712047701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984477743201355616063601 2988358307401016712047701)
                      ·
                        rfl

theorem cell23_5819807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_5819807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819807 prefixEnd_5819807 := by exact prefixLift 5819807
  have htrace : WordTrace (prefixWord ++ tailWord_5819807) baseStart_5819807 baseEnd_5819807 := by
    simpa [prefixWord, tailWord_5819807, baseEnd_5819807] using wordTrace_append hprefix tailTrace_5819807
  have hstable : (prefixWord ++ tailWord_5819807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819807).length < 2 ^ (prefixWord ++ tailWord_5819807).sum := by decide
  have hdescent : baseEnd_5819807 < baseStart_5819807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819877 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 5]
def baseStart_5819877 : Nat := 118140960795 + 5819877 * 2 ^ 59
def prefixEnd_5819877 : Nat := 4983230072969 + 3 ^ 40 * 5819877 * 2
def baseEnd_5819877 : Nat := 332043805671870159796931

theorem tailTrace_5819877 : CollatzResearch.WordTrace tailWord_5819877 prefixEnd_5819877 332043805671870159796931 := by
  unfold tailWord_5819877
  simp only [CollatzResearch.WordTrace]
  refine ⟨212268352736587059703841885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141512235157724706469227923 212268352736587059703841885)
  ·
    refine ⟨79600632276220147388940707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212268352736587059703841885 79600632276220147388940707)
    ·
      refine ⟨119400948414330221083411061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79600632276220147388940707 119400948414330221083411061)
      ·
        refine ⟨11193838913843458226569787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119400948414330221083411061 11193838913843458226569787)
        ·
          refine ⟨16790758370765187339854681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193838913843458226569787 16790758370765187339854681)
          ·
            refine ⟨12593068778073890504891011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16790758370765187339854681 12593068778073890504891011)
            ·
              refine ⟨18889603167110835757336517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12593068778073890504891011 18889603167110835757336517)
              ·
                refine ⟨3541800593833281704500597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18889603167110835757336517 3541800593833281704500597)
                ·
                  refine ⟨332043805671870159796931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541800593833281704500597 332043805671870159796931)
                  ·
                    rfl

theorem cell23_5819877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_5819877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819877 prefixEnd_5819877 := by exact prefixLift 5819877
  have htrace : WordTrace (prefixWord ++ tailWord_5819877) baseStart_5819877 baseEnd_5819877 := by
    simpa [prefixWord, tailWord_5819877, baseEnd_5819877] using wordTrace_append hprefix tailTrace_5819877
  have hstable : (prefixWord ++ tailWord_5819877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819877).length < 2 ^ (prefixWord ++ tailWord_5819877).sum := by decide
  have hdescent : baseEnd_5819877 < baseStart_5819877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819880 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5819880 : Nat := 118140960795 + 5819880 * 2 ^ 59
def prefixEnd_5819880 : Nat := 4983230072969 + 3 ^ 40 * 5819880 * 2
def baseEnd_5819880 : Nat := 2988395791488794926434865

theorem tailTrace_5819880 : CollatzResearch.WordTrace tailWord_5819880 prefixEnd_5819880 2988395791488794926434865 := by
  unfold tailWord_5819880
  simp only [CollatzResearch.WordTrace]
  refine ⟨106134231077788095608100547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141512308103717460810800729 106134231077788095608100547)
  ·
    refine ⟨159201346616682143412150821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106134231077788095608100547 159201346616682143412150821)
    ·
      refine ⟨29850252490627901889778279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159201346616682143412150821 29850252490627901889778279)
      ·
        refine ⟨44775378735941852834667419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29850252490627901889778279 44775378735941852834667419)
        ·
          refine ⟨67163068103912779252001129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44775378735941852834667419 67163068103912779252001129)
          ·
            refine ⟨50372301077934584439000847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67163068103912779252001129 50372301077934584439000847)
            ·
              refine ⟨75558451616901876658501271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50372301077934584439000847 75558451616901876658501271)
              ·
                refine ⟨113337677425352814987751907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75558451616901876658501271 113337677425352814987751907)
                ·
                  refine ⟨170006516138029222481627861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113337677425352814987751907 170006516138029222481627861)
                  ·
                    refine ⟨3984527721985059901913153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 170006516138029222481627861 3984527721985059901913153)
                    ·
                      refine ⟨2988395791488794926434865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984527721985059901913153 2988395791488794926434865)
                      ·
                        rfl

theorem cell23_5819880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5819880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819880 prefixEnd_5819880 := by exact prefixLift 5819880
  have htrace : WordTrace (prefixWord ++ tailWord_5819880) baseStart_5819880 baseEnd_5819880 := by
    simpa [prefixWord, tailWord_5819880, baseEnd_5819880] using wordTrace_append hprefix tailTrace_5819880
  have hstable : (prefixWord ++ tailWord_5819880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819880).length < 2 ^ (prefixWord ++ tailWord_5819880).sum := by decide
  have hdescent : baseEnd_5819880 < baseStart_5819880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819923 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_5819923 : Nat := 118140960795 + 5819923 * 2 ^ 59
def prefixEnd_5819923 : Nat := 4983230072969 + 3 ^ 40 * 5819923 * 2
def baseEnd_5819923 : Nat := 2988417871156938258197167

theorem tailTrace_5819923 : CollatzResearch.WordTrace tailWord_5819923 prefixEnd_5819923 2988417871156938258197167 := by
  unfold tailWord_5819923
  simp only [CollatzResearch.WordTrace]
  refine ⟨212270030494420409560016423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141513353662946939706677615 212270030494420409560016423)
  ·
    refine ⟨318405045741630614340024635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212270030494420409560016423 318405045741630614340024635)
    ·
      refine ⟨477607568612445921510036953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318405045741630614340024635 477607568612445921510036953)
      ·
        refine ⟨358205676459334441132527715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477607568612445921510036953 358205676459334441132527715)
        ·
          refine ⟨537308514689001661698791573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358205676459334441132527715 537308514689001661698791573)
          ·
            refine ⟨25186336626046952892130855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 537308514689001661698791573 25186336626046952892130855)
            ·
              refine ⟨37779504939070429338196283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25186336626046952892130855 37779504939070429338196283)
              ·
                refine ⟨56669257408605644007294425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37779504939070429338196283 56669257408605644007294425)
                ·
                  refine ⟨42501943056454233005470819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56669257408605644007294425 42501943056454233005470819)
                  ·
                    refine ⟨63752914584681349508206229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42501943056454233005470819 63752914584681349508206229)
                    ·
                      refine ⟨2988417871156938258197167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63752914584681349508206229 2988417871156938258197167)
                      ·
                        rfl

theorem cell23_5819923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_5819923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819923 prefixEnd_5819923 := by exact prefixLift 5819923
  have htrace : WordTrace (prefixWord ++ tailWord_5819923) baseStart_5819923 baseEnd_5819923 := by
    simpa [prefixWord, tailWord_5819923, baseEnd_5819923] using wordTrace_append hprefix tailTrace_5819923
  have hstable : (prefixWord ++ tailWord_5819923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819923).length < 2 ^ (prefixWord ++ tailWord_5819923).sum := by decide
  have hdescent : baseEnd_5819923 < baseStart_5819923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819930 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_5819930 : Nat := 118140960795 + 5819930 * 2 ^ 59
def prefixEnd_5819930 : Nat := 4983230072969 + 3 ^ 40 * 5819930 * 2
def baseEnd_5819930 : Nat := 2988421465521519730809635

theorem tailTrace_5819930 : CollatzResearch.WordTrace tailWord_5819930 prefixEnd_5819930 2988421465521519730809635 := by
  unfold tailWord_5819930
  simp only [CollatzResearch.WordTrace]
  refine ⟨53067571451348762438880311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141513523870263366503680829 53067571451348762438880311)
  ·
    refine ⟨79601357177023143658320467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53067571451348762438880311 79601357177023143658320467)
    ·
      refine ⟨119402035765534715487480701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79601357177023143658320467 119402035765534715487480701)
      ·
        refine ⟨44775763412075518307805263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119402035765534715487480701 44775763412075518307805263)
        ·
          refine ⟨67163645118113277461707895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44775763412075518307805263 67163645118113277461707895)
          ·
            refine ⟨100745467677169916192561843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67163645118113277461707895 100745467677169916192561843)
            ·
              refine ⟨151118201515754874288842765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100745467677169916192561843 151118201515754874288842765)
              ·
                refine ⟨56669325568408077858316037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151118201515754874288842765 56669325568408077858316037)
                ·
                  refine ⟨10625498544076514598434257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56669325568408077858316037 10625498544076514598434257)
                  ·
                    refine ⟨7969123908057385948825693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10625498544076514598434257 7969123908057385948825693)
                    ·
                      refine ⟨2988421465521519730809635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969123908057385948825693 2988421465521519730809635)
                      ·
                        rfl

theorem cell23_5819930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_5819930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819930 prefixEnd_5819930 := by exact prefixLift 5819930
  have htrace : WordTrace (prefixWord ++ tailWord_5819930) baseStart_5819930 baseEnd_5819930 := by
    simpa [prefixWord, tailWord_5819930, baseEnd_5819930] using wordTrace_append hprefix tailTrace_5819930
  have hstable : (prefixWord ++ tailWord_5819930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819930).length < 2 ^ (prefixWord ++ tailWord_5819930).sum := by decide
  have hdescent : baseEnd_5819930 < baseStart_5819930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819937 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_5819937 : Nat := 118140960795 + 5819937 * 2 ^ 59
def prefixEnd_5819937 : Nat := 4983230072969 + 3 ^ 40 * 5819937 * 2
def baseEnd_5819937 : Nat := 996141686628700401140701

theorem tailTrace_5819937 : CollatzResearch.WordTrace tailWord_5819937 prefixEnd_5819937 996141686628700401140701 := by
  unfold tailWord_5819937
  simp only [CollatzResearch.WordTrace]
  refine ⟨212270541116369689951026065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141513694077579793300684043 212270541116369689951026065)
  ·
    refine ⟨159202905837277267463269549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212270541116369689951026065 159202905837277267463269549)
    ·
      refine ⟨59701089688978975298726081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159202905837277267463269549 59701089688978975298726081)
      ·
        refine ⟨44775817266734231474044561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59701089688978975298726081 44775817266734231474044561)
        ·
          refine ⟨33581862950050673605533421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44775817266734231474044561 33581862950050673605533421)
          ·
            refine ⟨12593198606269002602075033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33581862950050673605533421 12593198606269002602075033)
            ·
              refine ⟨9444898954701751951556275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593198606269002602075033 9444898954701751951556275)
              ·
                refine ⟨14167348432052627927334413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444898954701751951556275 14167348432052627927334413)
                ·
                  refine ⟨5312755662019735472750405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14167348432052627927334413 5312755662019735472750405)
                  ·
                    refine ⟨996141686628700401140701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5312755662019735472750405 996141686628700401140701)
                    ·
                      rfl

theorem cell23_5819937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_5819937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819937 prefixEnd_5819937 := by exact prefixLift 5819937
  have htrace : WordTrace (prefixWord ++ tailWord_5819937) baseStart_5819937 baseEnd_5819937 := by
    simpa [prefixWord, tailWord_5819937, baseEnd_5819937] using wordTrace_append hprefix tailTrace_5819937
  have hstable : (prefixWord ++ tailWord_5819937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819937).length < 2 ^ (prefixWord ++ tailWord_5819937).sum := by decide
  have hdescent : baseEnd_5819937 < baseStart_5819937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819953 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_5819953 : Nat := 118140960795 + 5819953 * 2 ^ 59
def prefixEnd_5819953 : Nat := 4983230072969 + 3 ^ 40 * 5819953 * 2
def baseEnd_5819953 : Nat := 2988433275576573140822029

theorem tailTrace_5819953 : CollatzResearch.WordTrace tailWord_5819953 prefixEnd_5819953 2988433275576573140822029 := by
  unfold tailWord_5819953
  simp only [CollatzResearch.WordTrace]
  refine ⟨212271124684311724683608513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141514083122874483122405675 212271124684311724683608513)
  ·
    refine ⟨159203343513233793512706385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212271124684311724683608513 159203343513233793512706385)
    ·
      refine ⟨119402507634925345134529789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159203343513233793512706385 119402507634925345134529789)
      ·
        refine ⟨44775940363097004425448671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119402507634925345134529789 44775940363097004425448671)
        ·
          refine ⟨67163910544645506638173007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44775940363097004425448671 67163910544645506638173007)
          ·
            refine ⟨100745865816968259957259511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67163910544645506638173007 100745865816968259957259511)
            ·
              refine ⟨151118798725452389935889267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100745865816968259957259511 151118798725452389935889267)
              ·
                refine ⟨226678198088178584903833901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151118798725452389935889267 226678198088178584903833901)
                ·
                  refine ⟨85004324283066969338937713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226678198088178584903833901 85004324283066969338937713)
                  ·
                    refine ⟨63753243212300227004203285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85004324283066969338937713 63753243212300227004203285)
                    ·
                      refine ⟨2988433275576573140822029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63753243212300227004203285 2988433275576573140822029)
                      ·
                        rfl

theorem cell23_5819953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_5819953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819953 prefixEnd_5819953 := by exact prefixLift 5819953
  have htrace : WordTrace (prefixWord ++ tailWord_5819953) baseStart_5819953 baseEnd_5819953 := by
    simpa [prefixWord, tailWord_5819953, baseEnd_5819953] using wordTrace_append hprefix tailTrace_5819953
  have hstable : (prefixWord ++ tailWord_5819953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819953).length < 2 ^ (prefixWord ++ tailWord_5819953).sum := by decide
  have hdescent : baseEnd_5819953 < baseStart_5819953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5819994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_5819994 : Nat := 118140960795 + 5819994 * 2 ^ 59
def prefixEnd_5819994 : Nat := 4983230072969 + 3 ^ 40 * 5819994 * 2
def baseEnd_5819994 : Nat := 2988454328283407480409341

theorem tailTrace_5819994 : CollatzResearch.WordTrace tailWord_5819994 prefixEnd_5819994 2988454328283407480409341 := by
  unfold tailWord_5819994
  simp only [CollatzResearch.WordTrace]
  refine ⟨53068155019290797171462759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141515080051442125790567357 53068155019290797171462759)
  ·
    refine ⟨79602232528936195757194139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53068155019290797171462759 79602232528936195757194139)
    ·
      refine ⟨119403348793404293635791209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79602232528936195757194139 119403348793404293635791209)
      ·
        refine ⟨89552511595053220226843407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119403348793404293635791209 89552511595053220226843407)
        ·
          refine ⟨134328767392579830340265111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89552511595053220226843407 134328767392579830340265111)
          ·
            refine ⟨201493151088869745510397667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134328767392579830340265111 201493151088869745510397667)
            ·
              refine ⟨302239726633304618265596501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201493151088869745510397667 302239726633304618265596501)
              ·
                refine ⟨3541871796484038495299959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 302239726633304618265596501 3541871796484038495299959)
                ·
                  refine ⟨5312807694726057742949939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541871796484038495299959 5312807694726057742949939)
                  ·
                    refine ⟨7969211542089086614424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312807694726057742949939 7969211542089086614424909)
                    ·
                      refine ⟨2988454328283407480409341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969211542089086614424909 2988454328283407480409341)
                      ·
                        rfl

theorem cell23_5819994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_5819994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5819994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5819994 prefixEnd_5819994 := by exact prefixLift 5819994
  have htrace : WordTrace (prefixWord ++ tailWord_5819994) baseStart_5819994 baseEnd_5819994 := by
    simpa [prefixWord, tailWord_5819994, baseEnd_5819994] using wordTrace_append hprefix tailTrace_5819994
  have hstable : (prefixWord ++ tailWord_5819994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5819994).length < 2 ^ (prefixWord ++ tailWord_5819994).sum := by decide
  have hdescent : baseEnd_5819994 < baseStart_5819994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5819994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820000 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_5820000 : Nat := 118140960795 + 5820000 * 2 ^ 59
def prefixEnd_5820000 : Nat := 4983230072969 + 3 ^ 40 * 5820000 * 2
def baseEnd_5820000 : Nat := 2988457409167334456934313

theorem tailTrace_5820000 : CollatzResearch.WordTrace tailWord_5820000 prefixEnd_5820000 2988457409167334456934313 := by
  unfold tailWord_5820000
  simp only [CollatzResearch.WordTrace]
  refine ⟨106136419457570725855284727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141515225943427634473712969 106136419457570725855284727)
  ·
    refine ⟨159204629186356088782927091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106136419457570725855284727 159204629186356088782927091)
    ·
      refine ⟨238806943779534133174390637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159204629186356088782927091 238806943779534133174390637)
      ·
        refine ⟨89552603917325299940396489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238806943779534133174390637 89552603917325299940396489)
        ·
          refine ⟨67164452937993974955297367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89552603917325299940396489 67164452937993974955297367)
          ·
            refine ⟨100746679406990962432946051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67164452937993974955297367 100746679406990962432946051)
            ·
              refine ⟨151120019110486443649419077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100746679406990962432946051 151120019110486443649419077)
              ·
                refine ⟨28335003583216208184266077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151120019110486443649419077 28335003583216208184266077)
                ·
                  refine ⟨10625626343706078069099779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28335003583216208184266077 10625626343706078069099779)
                  ·
                    refine ⟨15938439515559117103649669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10625626343706078069099779 15938439515559117103649669)
                    ·
                      refine ⟨2988457409167334456934313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15938439515559117103649669 2988457409167334456934313)
                      ·
                        rfl

theorem cell23_5820000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_5820000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820000 prefixEnd_5820000 := by exact prefixLift 5820000
  have htrace : WordTrace (prefixWord ++ tailWord_5820000) baseStart_5820000 baseEnd_5820000 := by
    simpa [prefixWord, tailWord_5820000, baseEnd_5820000] using wordTrace_append hprefix tailTrace_5820000
  have hstable : (prefixWord ++ tailWord_5820000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820000).length < 2 ^ (prefixWord ++ tailWord_5820000).sum := by decide
  have hdescent : baseEnd_5820000 < baseStart_5820000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820021 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5820021 : Nat := 118140960795 + 5820021 * 2 ^ 59
def prefixEnd_5820021 : Nat := 4983230072969 + 3 ^ 40 * 5820021 * 2
def baseEnd_5820021 : Nat := 2988468192261078874771717

theorem tailTrace_5820021 : CollatzResearch.WordTrace tailWord_5820021 prefixEnd_5820021 2988468192261078874771717 := by
  unfold tailWord_5820021
  simp only [CollatzResearch.WordTrace]
  refine ⟨212273604848065372297083917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141515736565376914864722611 212273604848065372297083917)
  ·
    refine ⟨79602601818024514611406469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212273604848065372297083917 79602601818024514611406469)
    ·
      refine ⟨14925487840879596489638713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79602601818024514611406469 14925487840879596489638713)
      ·
        refine ⟨11194115880659697367229035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14925487840879596489638713 11194115880659697367229035)
        ·
          refine ⟨16791173820989546050843553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11194115880659697367229035 16791173820989546050843553)
          ·
            refine ⟨12593380365742159538132665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16791173820989546050843553 12593380365742159538132665)
            ·
              refine ⟨9445035274306619653599499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593380365742159538132665 9445035274306619653599499)
              ·
                refine ⟨14167552911459929480399249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445035274306619653599499 14167552911459929480399249)
                ·
                  refine ⟨10625664683594947110299437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167552911459929480399249 10625664683594947110299437)
                  ·
                    refine ⟨3984624256348105166362289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10625664683594947110299437 3984624256348105166362289)
                    ·
                      refine ⟨2988468192261078874771717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984624256348105166362289 2988468192261078874771717)
                      ·
                        rfl

theorem cell23_5820021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5820021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820021 prefixEnd_5820021 := by exact prefixLift 5820021
  have htrace : WordTrace (prefixWord ++ tailWord_5820021) baseStart_5820021 baseEnd_5820021 := by
    simpa [prefixWord, tailWord_5820021, baseEnd_5820021] using wordTrace_append hprefix tailTrace_5820021
  have hstable : (prefixWord ++ tailWord_5820021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820021).length < 2 ^ (prefixWord ++ tailWord_5820021).sum := by decide
  have hdescent : baseEnd_5820021 < baseStart_5820021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820040 : List Nat := [2, 1, 3, 5, 12]
def baseStart_5820040 : Nat := 118140960795 + 5820040 * 2 ^ 59
def prefixEnd_5820040 : Nat := 4983230072969 + 3 ^ 40 * 5820040 * 2
def baseEnd_5820040 : Nat := 4099421054037742524601

theorem tailTrace_5820040 : CollatzResearch.WordTrace tailWord_5820040 prefixEnd_5820040 4099421054037742524601 := by
  unfold tailWord_5820040
  simp only [CollatzResearch.WordTrace]
  refine ⟨106137148917498269271012787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141516198556664359028017049 106137148917498269271012787)
  ·
    refine ⟨159205723376247403906519181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106137148917498269271012787 159205723376247403906519181)
    ·
      refine ⟨59702146266092776464944693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159205723376247403906519181 59702146266092776464944693)
      ·
        refine ⟨5597076212446197793588565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59702146266092776464944693 5597076212446197793588565)
        ·
          refine ⟨4099421054037742524601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5597076212446197793588565 4099421054037742524601)
          ·
            rfl

theorem cell23_5820040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 12].length) (baseStart_5820040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820040 prefixEnd_5820040 := by exact prefixLift 5820040
  have htrace : WordTrace (prefixWord ++ tailWord_5820040) baseStart_5820040 baseEnd_5820040 := by
    simpa [prefixWord, tailWord_5820040, baseEnd_5820040] using wordTrace_append hprefix tailTrace_5820040
  have hstable : (prefixWord ++ tailWord_5820040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820040).length < 2 ^ (prefixWord ++ tailWord_5820040).sum := by decide
  have hdescent : baseEnd_5820040 < baseStart_5820040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820067 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3]
def baseStart_5820067 : Nat := 118140960795 + 5820067 * 2 ^ 59
def prefixEnd_5820067 : Nat := 4983230072969 + 3 ^ 40 * 5820067 * 2
def baseEnd_5820067 : Nat := 2988491812371185694796505

theorem tailTrace_5820067 : CollatzResearch.WordTrace tailWord_5820067 prefixEnd_5820067 2988491812371185694796505 := by
  unfold tailWord_5820067
  simp only [CollatzResearch.WordTrace]
  refine ⟨212275282605898722153258455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141516855070599148102172303 212275282605898722153258455)
  ·
    refine ⟨318412923908848083229887683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212275282605898722153258455 318412923908848083229887683)
    ·
      refine ⟨477619385863272124844831525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318412923908848083229887683 477619385863272124844831525)
      ·
        refine ⟨89553634849363523408405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477619385863272124844831525 89553634849363523408405911)
        ·
          refine ⟨134330452274045285112608867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89553634849363523408405911 134330452274045285112608867)
          ·
            refine ⟨201495678411067927668913301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134330452274045285112608867 201495678411067927668913301)
            ·
              refine ⟨9445109925518809109480311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201495678411067927668913301 9445109925518809109480311)
              ·
                refine ⟨14167664888278213664220467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445109925518809109480311 14167664888278213664220467)
                ·
                  refine ⟨21251497332417320496330701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14167664888278213664220467 21251497332417320496330701)
                  ·
                    refine ⟨7969311499656495186124013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21251497332417320496330701 7969311499656495186124013)
                    ·
                      refine ⟨2988491812371185694796505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969311499656495186124013 2988491812371185694796505)
                      ·
                        rfl

theorem cell23_5820067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_5820067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820067 prefixEnd_5820067 := by exact prefixLift 5820067
  have htrace : WordTrace (prefixWord ++ tailWord_5820067) baseStart_5820067 baseEnd_5820067 := by
    simpa [prefixWord, tailWord_5820067, baseEnd_5820067] using wordTrace_append hprefix tailTrace_5820067
  have hstable : (prefixWord ++ tailWord_5820067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820067).length < 2 ^ (prefixWord ++ tailWord_5820067).sum := by decide
  have hdescent : baseEnd_5820067 < baseStart_5820067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820072 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5820072 : Nat := 118140960795 + 5820072 * 2 ^ 59
def prefixEnd_5820072 : Nat := 4983230072969 + 3 ^ 40 * 5820072 * 2
def baseEnd_5820072 : Nat := 2988494379774458175233983

theorem tailTrace_5820072 : CollatzResearch.WordTrace tailWord_5820072 prefixEnd_5820072 2988494379774458175233983 := by
  unfold tailWord_5820072
  simp only [CollatzResearch.WordTrace]
  refine ⟨106137732485440304003595235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141516976647253738671460313 106137732485440304003595235)
  ·
    refine ⟨159206598728160456005392853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106137732485440304003595235 159206598728160456005392853)
    ·
      refine ⟨3731404657691260687626395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 159206598728160456005392853 3731404657691260687626395)
      ·
        refine ⟨5597106986536891031439593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731404657691260687626395 5597106986536891031439593)
        ·
          refine ⟨4197830239902668273579695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5597106986536891031439593 4197830239902668273579695)
          ·
            refine ⟨6296745359854002410369543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197830239902668273579695 6296745359854002410369543)
            ·
              refine ⟨9445118039781003615554315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296745359854002410369543 9445118039781003615554315)
              ·
                refine ⟨14167677059671505423331473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445118039781003615554315 14167677059671505423331473)
                ·
                  refine ⟨10625757794753629067498605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167677059671505423331473 10625757794753629067498605)
                  ·
                    refine ⟨3984659173032610900311977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10625757794753629067498605 3984659173032610900311977)
                    ·
                      refine ⟨2988494379774458175233983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984659173032610900311977 2988494379774458175233983)
                      ·
                        rfl

theorem cell23_5820072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5820072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820072 prefixEnd_5820072 := by exact prefixLift 5820072
  have htrace : WordTrace (prefixWord ++ tailWord_5820072) baseStart_5820072 baseEnd_5820072 := by
    simpa [prefixWord, tailWord_5820072, baseEnd_5820072] using wordTrace_append hprefix tailTrace_5820072
  have hstable : (prefixWord ++ tailWord_5820072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820072).length < 2 ^ (prefixWord ++ tailWord_5820072).sum := by decide
  have hdescent : baseEnd_5820072 < baseStart_5820072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820085 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5820085 : Nat := 118140960795 + 5820085 * 2 ^ 59
def prefixEnd_5820085 : Nat := 4983230072969 + 3 ^ 40 * 5820085 * 2
def baseEnd_5820085 : Nat := 2988501055022966624371423

theorem tailTrace_5820085 : CollatzResearch.WordTrace tailWord_5820085 prefixEnd_5820085 2988501055022966624371423 := by
  unfold tailWord_5820085
  simp only [CollatzResearch.WordTrace]
  refine ⟨212275939119833511227413709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141517292746555674151609139 212275939119833511227413709)
  ·
    refine ⟨79603477169937566710280141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212275939119833511227413709 79603477169937566710280141)
    ·
      refine ⟨29851303938726587516355053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79603477169937566710280141 29851303938726587516355053)
      ·
        refine ⟨11194238977022470318633145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29851303938726587516355053 11194238977022470318633145)
        ·
          refine ⟨8395679232766852738974859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11194238977022470318633145 8395679232766852738974859)
          ·
            refine ⟨12593518849150279108462289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395679232766852738974859 12593518849150279108462289)
            ·
              refine ⟨9445139136862709331346717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12593518849150279108462289 9445139136862709331346717)
              ·
                refine ⟨3541927176323515999255019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9445139136862709331346717 3541927176323515999255019)
                ·
                  refine ⟨5312890764485273998882529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541927176323515999255019 5312890764485273998882529)
                  ·
                    refine ⟨3984668073363955499161897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312890764485273998882529 3984668073363955499161897)
                    ·
                      refine ⟨2988501055022966624371423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984668073363955499161897 2988501055022966624371423)
                      ·
                        rfl

theorem cell23_5820085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5820085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820085 prefixEnd_5820085 := by exact prefixLift 5820085
  have htrace : WordTrace (prefixWord ++ tailWord_5820085) baseStart_5820085 baseEnd_5820085 := by
    simpa [prefixWord, tailWord_5820085, baseEnd_5820085] using wordTrace_append hprefix tailTrace_5820085
  have hstable : (prefixWord ++ tailWord_5820085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820085).length < 2 ^ (prefixWord ++ tailWord_5820085).sum := by decide
  have hdescent : baseEnd_5820085 < baseStart_5820085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820102 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5820102 : Nat := 118140960795 + 5820102 * 2 ^ 59
def prefixEnd_5820102 : Nat := 4983230072969 + 3 ^ 40 * 5820102 * 2
def baseEnd_5820102 : Nat := 2988509784194093057858845

theorem tailTrace_5820102 : CollatzResearch.WordTrace tailWord_5820102 prefixEnd_5820102 2988509784194093057858845 := by
  unfold tailWord_5820102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633642473774122597836955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141517706107181282087188373 6633642473774122597836955)
  ·
    refine ⟨9950463710661183896755433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633642473774122597836955 9950463710661183896755433)
    ·
      refine ⟨7462847782995887922566575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9950463710661183896755433 7462847782995887922566575)
      ·
        refine ⟨11194271674493831883849863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462847782995887922566575 11194271674493831883849863)
        ·
          refine ⟨16791407511740747825774795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11194271674493831883849863 16791407511740747825774795)
          ·
            refine ⟨25187111267611121738662193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16791407511740747825774795 25187111267611121738662193)
            ·
              refine ⟨18890333450708341303996645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25187111267611121738662193 18890333450708341303996645)
              ·
                refine ⟨3541937522007813994499371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18890333450708341303996645 3541937522007813994499371)
                ·
                  refine ⟨5312906283011720991749057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541937522007813994499371 5312906283011720991749057)
                  ·
                    refine ⟨3984679712258790743811793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312906283011720991749057 3984679712258790743811793)
                    ·
                      refine ⟨2988509784194093057858845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984679712258790743811793 2988509784194093057858845)
                      ·
                        rfl

theorem cell23_5820102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5820102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820102 prefixEnd_5820102 := by exact prefixLift 5820102
  have htrace : WordTrace (prefixWord ++ tailWord_5820102) baseStart_5820102 baseEnd_5820102 := by
    simpa [prefixWord, tailWord_5820102, baseEnd_5820102] using wordTrace_append hprefix tailTrace_5820102
  have hstable : (prefixWord ++ tailWord_5820102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820102).length < 2 ^ (prefixWord ++ tailWord_5820102).sum := by decide
  have hdescent : baseEnd_5820102 < baseStart_5820102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820107 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 4, 2]
def baseStart_5820107 : Nat := 118140960795 + 5820107 * 2 ^ 59
def prefixEnd_5820107 : Nat := 4983230072969 + 3 ^ 40 * 5820107 * 2
def baseEnd_5820107 : Nat := 2988512351597365538296321

theorem tailTrace_5820107 : CollatzResearch.WordTrace tailWord_5820107 prefixEnd_5820107 2988512351597365538296321 := by
  unfold tailWord_5820107
  simp only [CollatzResearch.WordTrace]
  refine ⟨212276741525753808984714575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141517827683835872656476383 212276741525753808984714575)
  ·
    refine ⟨318415112288630713477071863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212276741525753808984714575 318415112288630713477071863)
    ·
      refine ⟨477622668432946070215607795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318415112288630713477071863 477622668432946070215607795)
      ·
        refine ⟨716434002649419105323411693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477622668432946070215607795 716434002649419105323411693)
        ·
          refine ⟨268662750993532164496279385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716434002649419105323411693 268662750993532164496279385)
          ·
            refine ⟨201497063245149123372209539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268662750993532164496279385 201497063245149123372209539)
            ·
              refine ⟨302245594867723685058314309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201497063245149123372209539 302245594867723685058314309)
              ·
                refine ⟨56671049037698190948433933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302245594867723685058314309 56671049037698190948433933)
                ·
                  refine ⟨21251643389136821605662725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56671049037698190948433933 21251643389136821605662725)
                  ·
                    refine ⟨3984683135463154051061761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21251643389136821605662725 3984683135463154051061761)
                    ·
                      refine ⟨2988512351597365538296321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984683135463154051061761 2988512351597365538296321)
                      ·
                        rfl

theorem cell23_5820107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4, 2].length) (baseStart_5820107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820107 prefixEnd_5820107 := by exact prefixLift 5820107
  have htrace : WordTrace (prefixWord ++ tailWord_5820107) baseStart_5820107 baseEnd_5820107 := by
    simpa [prefixWord, tailWord_5820107, baseEnd_5820107] using wordTrace_append hprefix tailTrace_5820107
  have hstable : (prefixWord ++ tailWord_5820107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820107).length < 2 ^ (prefixWord ++ tailWord_5820107).sum := by decide
  have hdescent : baseEnd_5820107 < baseStart_5820107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820141 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5820141 : Nat := 118140960795 + 5820141 * 2 ^ 59
def prefixEnd_5820141 : Nat := 4983230072969 + 3 ^ 40 * 5820141 * 2
def baseEnd_5820141 : Nat := 2988529809939618405271165

theorem tailTrace_5820141 : CollatzResearch.WordTrace tailWord_5820141 prefixEnd_5820141 2988529809939618405271165 := by
  unfold tailWord_5820141
  simp only [CollatzResearch.WordTrace]
  refine ⟨212277981607630632791452277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141518654405087088527634851 212277981607630632791452277)
  ·
    refine ⟨19901060775715371824198651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212277981607630632791452277 19901060775715371824198651)
    ·
      refine ⟨29851591163573057736297977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19901060775715371824198651 29851591163573057736297977)
      ·
        refine ⟨22388693372679793302223483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29851591163573057736297977 22388693372679793302223483)
        ·
          refine ⟨33583040059019689953335225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22388693372679793302223483 33583040059019689953335225)
          ·
            refine ⟨25187280044264767465001419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33583040059019689953335225 25187280044264767465001419)
            ·
              refine ⟨37780920066397151197502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25187280044264767465001419 37780920066397151197502129)
              ·
                refine ⟨28335690049797863398126597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37780920066397151197502129 28335690049797863398126597)
                ·
                  refine ⟨5312941884337099387148737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28335690049797863398126597 5312941884337099387148737)
                  ·
                    refine ⟨3984706413252824540361553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5312941884337099387148737 3984706413252824540361553)
                    ·
                      refine ⟨2988529809939618405271165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984706413252824540361553 2988529809939618405271165)
                      ·
                        rfl

theorem cell23_5820141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5820141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820141 prefixEnd_5820141 := by exact prefixLift 5820141
  have htrace : WordTrace (prefixWord ++ tailWord_5820141) baseStart_5820141 baseEnd_5820141 := by
    simpa [prefixWord, tailWord_5820141, baseEnd_5820141] using wordTrace_append hprefix tailTrace_5820141
  have hstable : (prefixWord ++ tailWord_5820141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820141).length < 2 ^ (prefixWord ++ tailWord_5820141).sum := by decide
  have hdescent : baseEnd_5820141 < baseStart_5820141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820157 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_5820157 : Nat := 118140960795 + 5820157 * 2 ^ 59
def prefixEnd_5820157 : Nat := 4983230072969 + 3 ^ 40 * 5820157 * 2
def baseEnd_5820157 : Nat := 2988538025630090342671091

theorem tailTrace_5820157 : CollatzResearch.WordTrace tailWord_5820157 prefixEnd_5820157 2988538025630090342671091 := by
  unfold tailWord_5820157
  simp only [CollatzResearch.WordTrace]
  refine ⟨212278565175572667524034725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141519043450381778349356483 212278565175572667524034725)
  ·
    refine ⟨39802230970419875160756511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212278565175572667524034725 39802230970419875160756511)
    ·
      refine ⟨59703346455629812741134767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39802230970419875160756511 59703346455629812741134767)
      ·
        refine ⟨89555019683444719111702151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59703346455629812741134767 89555019683444719111702151)
        ·
          refine ⟨134332529525167078667553227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89555019683444719111702151 134332529525167078667553227)
          ·
            refine ⟨201498794287750618001329841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134332529525167078667553227 201498794287750618001329841)
            ·
              refine ⟨151124095715812963500997381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201498794287750618001329841 151124095715812963500997381)
              ·
                refine ⟨28335767946714930656437009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151124095715812963500997381 28335767946714930656437009)
                ·
                  refine ⟨21251825960036197992327757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28335767946714930656437009 21251825960036197992327757)
                  ·
                    refine ⟨7969434735013574247122909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21251825960036197992327757 7969434735013574247122909)
                    ·
                      refine ⟨2988538025630090342671091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969434735013574247122909 2988538025630090342671091)
                      ·
                        rfl

theorem cell23_5820157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_5820157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820157 prefixEnd_5820157 := by exact prefixLift 5820157
  have htrace : WordTrace (prefixWord ++ tailWord_5820157) baseStart_5820157 baseEnd_5820157 := by
    simpa [prefixWord, tailWord_5820157, baseEnd_5820157] using wordTrace_append hprefix tailTrace_5820157
  have hstable : (prefixWord ++ tailWord_5820157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820157).length < 2 ^ (prefixWord ++ tailWord_5820157).sum := by decide
  have hdescent : baseEnd_5820157 < baseStart_5820157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820164 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 7]
def baseStart_5820164 : Nat := 118140960795 + 5820164 * 2 ^ 59
def prefixEnd_5820164 : Nat := 4983230072969 + 3 ^ 40 * 5820164 * 2
def baseEnd_5820164 : Nat := 332060179999407979475951

theorem tailTrace_5820164 : CollatzResearch.WordTrace tailWord_5820164 prefixEnd_5820164 332060179999407979475951 := by
  unfold tailWord_5820164
  simp only [CollatzResearch.WordTrace]
  refine ⟨106139410243273653859769773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141519213657698205146359697 106139410243273653859769773)
  ·
    refine ⟨39802278841227620197413665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106139410243273653859769773 39802278841227620197413665)
    ·
      refine ⟨29851709130920715148060249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39802278841227620197413665 29851709130920715148060249)
      ·
        refine ⟨22388781848190536361045187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29851709130920715148060249 22388781848190536361045187)
        ·
          refine ⟨33583172772285804541567781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22388781848190536361045187 33583172772285804541567781)
          ·
            refine ⟨6296844894803588351543959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33583172772285804541567781 6296844894803588351543959)
            ·
              refine ⟨9445267342205382527315939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296844894803588351543959 9445267342205382527315939)
              ·
                refine ⟨14167901013308073790973909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445267342205382527315939 14167901013308073790973909)
                ·
                  refine ⟨332060179999407979475951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14167901013308073790973909 332060179999407979475951)
                  ·
                    rfl

theorem cell23_5820164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_5820164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820164 prefixEnd_5820164 := by exact prefixLift 5820164
  have htrace : WordTrace (prefixWord ++ tailWord_5820164) baseStart_5820164 baseEnd_5820164 := by
    simpa [prefixWord, tailWord_5820164, baseEnd_5820164] using wordTrace_append hprefix tailTrace_5820164
  have hstable : (prefixWord ++ tailWord_5820164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820164).length < 2 ^ (prefixWord ++ tailWord_5820164).sum := by decide
  have hdescent : baseEnd_5820164 < baseStart_5820164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820194 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_5820194 : Nat := 118140960795 + 5820194 * 2 ^ 59
def prefixEnd_5820194 : Nat := 4983230072969 + 3 ^ 40 * 5820194 * 2
def baseEnd_5820194 : Nat := 996185674804768899302807

theorem tailTrace_5820194 : CollatzResearch.WordTrace tailWord_5820194 prefixEnd_5820194 996185674804768899302807 := by
  unfold tailWord_5820194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53069978669109655710782909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141519943117625748562087757 53069978669109655710782909)
  ·
    refine ⟨19901242000916120891543591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53069978669109655710782909 19901242000916120891543591)
    ·
      refine ⟨29851863001374181337315387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19901242000916120891543591 29851863001374181337315387)
      ·
        refine ⟨44777794502061272005973081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29851863001374181337315387 44777794502061272005973081)
        ·
          refine ⟨33583345876545954004479811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44777794502061272005973081 33583345876545954004479811)
          ·
            refine ⟨50375018814818931006719717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33583345876545954004479811 50375018814818931006719717)
            ·
              refine ⟨9445316027778549563759947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50375018814818931006719717 9445316027778549563759947)
              ·
                refine ⟨14167974041667824345639921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445316027778549563759947 14167974041667824345639921)
                ·
                  refine ⟨10625980531250868259229941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167974041667824345639921 10625980531250868259229941)
                  ·
                    refine ⟨996185674804768899302807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10625980531250868259229941 996185674804768899302807)
                    ·
                      rfl

theorem cell23_5820194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_5820194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820194 prefixEnd_5820194 := by exact prefixLift 5820194
  have htrace : WordTrace (prefixWord ++ tailWord_5820194) baseStart_5820194 baseEnd_5820194 := by
    simpa [prefixWord, tailWord_5820194, baseEnd_5820194] using wordTrace_append hprefix tailTrace_5820194
  have hstable : (prefixWord ++ tailWord_5820194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820194).length < 2 ^ (prefixWord ++ tailWord_5820194).sum := by decide
  have hdescent : baseEnd_5820194 < baseStart_5820194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820207 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 5, 4]
def baseStart_5820207 : Nat := 118140960795 + 5820207 * 2 ^ 59
def prefixEnd_5820207 : Nat := 4983230072969 + 3 ^ 40 * 5820207 * 2
def baseEnd_5820207 : Nat := 996187899887605049015287

theorem tailTrace_5820207 : CollatzResearch.WordTrace tailWord_5820207 prefixEnd_5820207 996187899887605049015287 := by
  unfold tailWord_5820207
  simp only [CollatzResearch.WordTrace]
  refine ⟨212280388825391526063354875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141520259216927684042236583 212280388825391526063354875)
  ·
    refine ⟨318420583238087289095032313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212280388825391526063354875 318420583238087289095032313)
    ·
      refine ⟨238815437428565466821274235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318420583238087289095032313 238815437428565466821274235)
      ·
        refine ⟨358223156142848200231911353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238815437428565466821274235 358223156142848200231911353)
        ·
          refine ⟨268667367107136150173933515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358223156142848200231911353 268667367107136150173933515)
          ·
            refine ⟨403001050660704225260900273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268667367107136150173933515 403001050660704225260900273)
            ·
              refine ⟨302250787995528168945675205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403001050660704225260900273 302250787995528168945675205)
              ·
                refine ⟨56672022749161531677314101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302250787995528168945675205 56672022749161531677314101)
                ·
                  refine ⟨5313002132733893594748197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56672022749161531677314101 5313002132733893594748197)
                  ·
                    refine ⟨996187899887605049015287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313002132733893594748197 996187899887605049015287)
                    ·
                      rfl

theorem cell23_5820207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_5820207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820207 prefixEnd_5820207 := by exact prefixLift 5820207
  have htrace : WordTrace (prefixWord ++ tailWord_5820207) baseStart_5820207 baseEnd_5820207 := by
    simpa [prefixWord, tailWord_5820207, baseEnd_5820207] using wordTrace_append hprefix tailTrace_5820207
  have hstable : (prefixWord ++ tailWord_5820207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820207).length < 2 ^ (prefixWord ++ tailWord_5820207).sum := by decide
  have hdescent : baseEnd_5820207 < baseStart_5820207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820258 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5820258 : Nat := 118140960795 + 5820258 * 2 ^ 59
def prefixEnd_5820258 : Nat := 4983230072969 + 3 ^ 40 * 5820258 * 2
def baseEnd_5820258 : Nat := 996196629058731482502709

theorem tailTrace_5820258 : CollatzResearch.WordTrace tailWord_5820258 prefixEnd_5820258 996196629058731482502709 := by
  unfold tailWord_5820258
  simp only [CollatzResearch.WordTrace]
  refine ⟨53070562237051690443365357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141521499298804507848974285 53070562237051690443365357)
  ·
    refine ⟨19901460838894383916262009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53070562237051690443365357 19901460838894383916262009)
    ·
      refine ⟨14926095629170787937196507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19901460838894383916262009 14926095629170787937196507)
      ·
        refine ⟨22389143443756181905794761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926095629170787937196507 22389143443756181905794761)
        ·
          refine ⟨16791857582817136429346071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389143443756181905794761 16791857582817136429346071)
          ·
            refine ⟨25187786374225704644019107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16791857582817136429346071 25187786374225704644019107)
            ·
              refine ⟨37781679561338556966028661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25187786374225704644019107 37781679561338556966028661)
              ·
                refine ⟨3542032458875489715565187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37781679561338556966028661 3542032458875489715565187)
                ·
                  refine ⟨5313048688313234573347781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542032458875489715565187 5313048688313234573347781)
                  ·
                    refine ⟨996196629058731482502709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313048688313234573347781 996196629058731482502709)
                    ·
                      rfl

theorem cell23_5820258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5820258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820258 prefixEnd_5820258 := by exact prefixLift 5820258
  have htrace : WordTrace (prefixWord ++ tailWord_5820258) baseStart_5820258 baseEnd_5820258 := by
    simpa [prefixWord, tailWord_5820258, baseEnd_5820258] using wordTrace_append hprefix tailTrace_5820258
  have hstable : (prefixWord ++ tailWord_5820258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820258).length < 2 ^ (prefixWord ++ tailWord_5820258).sum := by decide
  have hdescent : baseEnd_5820258 < baseStart_5820258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820281 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_5820281 : Nat := 118140960795 + 5820281 * 2 ^ 59
def prefixEnd_5820281 : Nat := 4983230072969 + 3 ^ 40 * 5820281 * 2
def baseEnd_5820281 : Nat := 2988601697231247857520521

theorem tailTrace_5820281 : CollatzResearch.WordTrace tailWord_5820281 prefixEnd_5820281 2988601697231247857520521 := by
  unfold tailWord_5820281
  simp only [CollatzResearch.WordTrace]
  refine ⟨212283087827123436701548697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141522058551415624467699131 212283087827123436701548697)
  ·
    refine ⟨159212315870342577526161523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212283087827123436701548697 159212315870342577526161523)
    ·
      refine ⟨238818473805513866289242285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159212315870342577526161523 238818473805513866289242285)
      ·
        refine ⟨89556927677067699858465857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238818473805513866289242285 89556927677067699858465857)
        ·
          refine ⟨67167695757800774893849393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89556927677067699858465857 67167695757800774893849393)
          ·
            refine ⟨50375771818350581170387045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67167695757800774893849393 50375771818350581170387045)
            ·
              refine ⟨9445457215940733969447571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50375771818350581170387045 9445457215940733969447571)
              ·
                refine ⟨14168185823911100954171357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445457215940733969447571 14168185823911100954171357)
                ·
                  refine ⟨5313069683966662857814259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14168185823911100954171357 5313069683966662857814259)
                  ·
                    refine ⟨7969604525949994286721389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313069683966662857814259 7969604525949994286721389)
                    ·
                      refine ⟨2988601697231247857520521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969604525949994286721389 2988601697231247857520521)
                      ·
                        rfl

theorem cell23_5820281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_5820281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820281 prefixEnd_5820281 := by exact prefixLift 5820281
  have htrace : WordTrace (prefixWord ++ tailWord_5820281) baseStart_5820281 baseEnd_5820281 := by
    simpa [prefixWord, tailWord_5820281, baseEnd_5820281] using wordTrace_append hprefix tailTrace_5820281
  have hstable : (prefixWord ++ tailWord_5820281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820281).length < 2 ^ (prefixWord ++ tailWord_5820281).sum := by decide
  have hdescent : baseEnd_5820281 < baseStart_5820281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_5820304 : Nat := 118140960795 + 5820304 * 2 ^ 59
def prefixEnd_5820304 : Nat := 4983230072969 + 3 ^ 40 * 5820304 * 2
def baseEnd_5820304 : Nat := 2988613507286301267532915

theorem tailTrace_5820304 : CollatzResearch.WordTrace tailWord_5820304 prefixEnd_5820304 2988613507286301267532915 := by
  unfold tailWord_5820304
  simp only [CollatzResearch.WordTrace]
  refine ⟨106141963353020055814817983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141522617804026741086423977 106141963353020055814817983)
  ·
    refine ⟨159212945029530083722226975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106141963353020055814817983 159212945029530083722226975)
    ·
      refine ⟨238819417544295125583340463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159212945029530083722226975 238819417544295125583340463)
      ·
        refine ⟨358229126316442688375010695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238819417544295125583340463 358229126316442688375010695)
        ·
          refine ⟨537343689474664032562516043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358229126316442688375010695 537343689474664032562516043)
          ·
            refine ⟨806015534211996048843774065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537343689474664032562516043 806015534211996048843774065)
            ·
              refine ⟨604511650658997036632830549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806015534211996048843774065 604511650658997036632830549)
              ·
                refine ⟨7084120906160121523040983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 604511650658997036632830549 7084120906160121523040983)
                ·
                  refine ⟨10626181359240182284561475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7084120906160121523040983 10626181359240182284561475)
                  ·
                    refine ⟨15939272038860273426842213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10626181359240182284561475 15939272038860273426842213)
                    ·
                      refine ⟨2988613507286301267532915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15939272038860273426842213 2988613507286301267532915)
                      ·
                        rfl

theorem cell23_5820304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_5820304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820304 prefixEnd_5820304 := by exact prefixLift 5820304
  have htrace : WordTrace (prefixWord ++ tailWord_5820304) baseStart_5820304 baseEnd_5820304 := by
    simpa [prefixWord, tailWord_5820304, baseEnd_5820304] using wordTrace_append hprefix tailTrace_5820304
  have hstable : (prefixWord ++ tailWord_5820304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820304).length < 2 ^ (prefixWord ++ tailWord_5820304).sum := by decide
  have hdescent : baseEnd_5820304 < baseStart_5820304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820324 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_5820324 : Nat := 118140960795 + 5820324 * 2 ^ 59
def prefixEnd_5820324 : Nat := 4983230072969 + 3 ^ 40 * 5820324 * 2
def baseEnd_5820324 : Nat := 2988623776899391189282823

theorem tailTrace_5820324 : CollatzResearch.WordTrace tailWord_5820324 prefixEnd_5820324 2988623776899391189282823 := by
  unfold tailWord_5820324
  simp only [CollatzResearch.WordTrace]
  refine ⟨106142328082983827522682013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141523104110645103363576017 106142328082983827522682013)
  ·
    refine ⟨39803373031118935321005755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106142328082983827522682013 39803373031118935321005755)
    ·
      refine ⟨59705059546678402981508633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39803373031118935321005755 59705059546678402981508633)
      ·
        refine ⟨44778794660008802236131475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59705059546678402981508633 44778794660008802236131475)
        ·
          refine ⟨67168191990013203354197213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44778794660008802236131475 67168191990013203354197213)
          ·
            refine ⟨25188071996254951257823955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67168191990013203354197213 25188071996254951257823955)
            ·
              refine ⟨37782107994382426886735933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25188071996254951257823955 37782107994382426886735933)
              ·
                refine ⟨14168290497893410082525975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37782107994382426886735933 14168290497893410082525975)
                ·
                  refine ⟨21252435746840115123788963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14168290497893410082525975 21252435746840115123788963)
                  ·
                    refine ⟨31878653620260172685683445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21252435746840115123788963 31878653620260172685683445)
                    ·
                      refine ⟨2988623776899391189282823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31878653620260172685683445 2988623776899391189282823)
                      ·
                        rfl

theorem cell23_5820324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_5820324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820324 prefixEnd_5820324 := by exact prefixLift 5820324
  have htrace : WordTrace (prefixWord ++ tailWord_5820324) baseStart_5820324 baseEnd_5820324 := by
    simpa [prefixWord, tailWord_5820324, baseEnd_5820324] using wordTrace_append hprefix tailTrace_5820324
  have hstable : (prefixWord ++ tailWord_5820324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820324).length < 2 ^ (prefixWord ++ tailWord_5820324).sum := by decide
  have hdescent : baseEnd_5820324 < baseStart_5820324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820357 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_5820357 : Nat := 118140960795 + 5820357 * 2 ^ 59
def prefixEnd_5820357 : Nat := 4983230072969 + 3 ^ 40 * 5820357 * 2
def baseEnd_5820357 : Nat := 996213573920329853390057

theorem tailTrace_5820357 : CollatzResearch.WordTrace tailWord_5820357 prefixEnd_5820357 996213573920329853390057 := by
  unfold tailWord_5820357
  simp only [CollatzResearch.WordTrace]
  refine ⟨212285859774848101681315325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141523906516565401120876883 212285859774848101681315325)
  ·
    refine ⟨79607197415568038130493247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212285859774848101681315325 79607197415568038130493247)
    ·
      refine ⟨119410796123352057195739871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79607197415568038130493247 119410796123352057195739871)
      ·
        refine ⟨179116194185028085793609807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119410796123352057195739871 179116194185028085793609807)
        ·
          refine ⟨268674291277542128690414711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179116194185028085793609807 268674291277542128690414711)
          ·
            refine ⟨403011436916313193035622067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268674291277542128690414711 403011436916313193035622067)
            ·
              refine ⟨604517155374469789553433101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403011436916313193035622067 604517155374469789553433101)
              ·
                refine ⟨226693933265426171082537413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604517155374469789553433101 226693933265426171082537413)
                ·
                  refine ⟨42505112487267407077975765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226693933265426171082537413 42505112487267407077975765)
                  ·
                    refine ⟨996213573920329853390057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42505112487267407077975765 996213573920329853390057)
                    ·
                      rfl

theorem cell23_5820357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_5820357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820357 prefixEnd_5820357 := by exact prefixLift 5820357
  have htrace : WordTrace (prefixWord ++ tailWord_5820357) baseStart_5820357 baseEnd_5820357 := by
    simpa [prefixWord, tailWord_5820357, baseEnd_5820357] using wordTrace_append hprefix tailTrace_5820357
  have hstable : (prefixWord ++ tailWord_5820357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820357).length < 2 ^ (prefixWord ++ tailWord_5820357).sum := by decide
  have hdescent : baseEnd_5820357 < baseStart_5820357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820388 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_5820388 : Nat := 118140960795 + 5820388 * 2 ^ 59
def prefixEnd_5820388 : Nat := 4983230072969 + 3 ^ 40 * 5820388 * 2
def baseEnd_5820388 : Nat := 2988656639661278938882529

theorem tailTrace_5820388 : CollatzResearch.WordTrace tailWord_5820388 prefixEnd_5820388 2988656639661278938882529 := by
  unfold tailWord_5820388
  simp only [CollatzResearch.WordTrace]
  refine ⟨106143495218867896987846909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141524660291823862650462545 106143495218867896987846909)
  ·
    refine ⟨39803810707075461370442591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106143495218867896987846909 39803810707075461370442591)
    ·
      refine ⟨59705716060613192055663887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39803810707075461370442591 59705716060613192055663887)
      ·
        refine ⟨89558574090919788083495831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59705716060613192055663887 89558574090919788083495831)
        ·
          refine ⟨134337861136379682125243747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89558574090919788083495831 134337861136379682125243747)
          ·
            refine ⟨201506791704569523187865621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134337861136379682125243747 201506791704569523187865621)
            ·
              refine ⟨9445630861151696399431201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201506791704569523187865621 9445630861151696399431201)
              ·
                refine ⟨7084223145863772299573401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9445630861151696399431201 7084223145863772299573401)
                ·
                  refine ⟨5313167359397829224680051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7084223145863772299573401 5313167359397829224680051)
                  ·
                    refine ⟨7969751039096743837020077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313167359397829224680051 7969751039096743837020077)
                    ·
                      refine ⟨2988656639661278938882529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969751039096743837020077 2988656639661278938882529)
                      ·
                        rfl

theorem cell23_5820388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_5820388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820388 prefixEnd_5820388 := by exact prefixLift 5820388
  have htrace : WordTrace (prefixWord ++ tailWord_5820388) baseStart_5820388 baseEnd_5820388 := by
    simpa [prefixWord, tailWord_5820388, baseEnd_5820388] using wordTrace_append hprefix tailTrace_5820388
  have hstable : (prefixWord ++ tailWord_5820388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820388).length < 2 ^ (prefixWord ++ tailWord_5820388).sum := by decide
  have hdescent : baseEnd_5820388 < baseStart_5820388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820394 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_5820394 : Nat := 118140960795 + 5820394 * 2 ^ 59
def prefixEnd_5820394 : Nat := 4983230072969 + 3 ^ 40 * 5820394 * 2
def baseEnd_5820394 : Nat := 2988659720545205915407501

theorem tailTrace_5820394 : CollatzResearch.WordTrace tailWord_5820394 prefixEnd_5820394 2988659720545205915407501 := by
  unfold tailWord_5820394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53071802318928514250103059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141524806183809371333608157 53071802318928514250103059)
  ·
    refine ⟨79607703478392771375154589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53071802318928514250103059 79607703478392771375154589)
    ·
      refine ⟨29852888804397289265682971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79607703478392771375154589 29852888804397289265682971)
      ·
        refine ⟨44779333206595933898524457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29852888804397289265682971 44779333206595933898524457)
        ·
          refine ⟨33584499904946950423893343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44779333206595933898524457 33584499904946950423893343)
          ·
            refine ⟨50376749857420425635840015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33584499904946950423893343 50376749857420425635840015)
            ·
              refine ⟨75565124786130638453760023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50376749857420425635840015 75565124786130638453760023)
              ·
                refine ⟨113347687179195957680640035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75565124786130638453760023 113347687179195957680640035)
                ·
                  refine ⟨170021530768793936520960053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113347687179195957680640035 170021530768793936520960053)
                  ·
                    refine ⟨15939518509574431548840005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170021530768793936520960053 15939518509574431548840005)
                    ·
                      refine ⟨2988659720545205915407501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15939518509574431548840005 2988659720545205915407501)
                      ·
                        rfl

theorem cell23_5820394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_5820394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820394 prefixEnd_5820394 := by exact prefixLift 5820394
  have htrace : WordTrace (prefixWord ++ tailWord_5820394) baseStart_5820394 baseEnd_5820394 := by
    simpa [prefixWord, tailWord_5820394, baseEnd_5820394] using wordTrace_append hprefix tailTrace_5820394
  have hstable : (prefixWord ++ tailWord_5820394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820394).length < 2 ^ (prefixWord ++ tailWord_5820394).sum := by decide
  have hdescent : baseEnd_5820394 < baseStart_5820394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820398 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_5820398 : Nat := 118140960795 + 5820398 * 2 ^ 59
def prefixEnd_5820398 : Nat := 4983230072969 + 3 ^ 40 * 5820398 * 2
def baseEnd_5820398 : Nat := 2988661774467823899757483

theorem tailTrace_5820398 : CollatzResearch.WordTrace tailWord_5820398 prefixEnd_5820398 2988661774467823899757483 := by
  unfold tailWord_5820398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535919395962445710444731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141524903445133043789038565 26535919395962445710444731)
  ·
    refine ⟨39803879093943668565667097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26535919395962445710444731 39803879093943668565667097)
    ·
      refine ⟨29852909320457751424250323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39803879093943668565667097 29852909320457751424250323)
      ·
        refine ⟨44779363980686627136375485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29852909320457751424250323 44779363980686627136375485)
        ·
          refine ⟨16792261492757485176140807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44779363980686627136375485 16792261492757485176140807)
          ·
            refine ⟨25188392239136227764211211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16792261492757485176140807 25188392239136227764211211)
            ·
              refine ⟨37782588358704341646316817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25188392239136227764211211 37782588358704341646316817)
              ·
                refine ⟨28336941269028256234737613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37782588358704341646316817 28336941269028256234737613)
                ·
                  refine ⟨10626352975885596088026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28336941269028256234737613 10626352975885596088026605)
                  ·
                    refine ⟨3984882365957098533009977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10626352975885596088026605 3984882365957098533009977)
                    ·
                      refine ⟨2988661774467823899757483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984882365957098533009977 2988661774467823899757483)
                      ·
                        rfl

theorem cell23_5820398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_5820398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820398 prefixEnd_5820398 := by exact prefixLift 5820398
  have htrace : WordTrace (prefixWord ++ tailWord_5820398) baseStart_5820398 baseEnd_5820398 := by
    simpa [prefixWord, tailWord_5820398, baseEnd_5820398] using wordTrace_append hprefix tailTrace_5820398
  have hstable : (prefixWord ++ tailWord_5820398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820398).length < 2 ^ (prefixWord ++ tailWord_5820398).sum := by decide
  have hdescent : baseEnd_5820398 < baseStart_5820398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820411 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 4, 2]
def baseStart_5820411 : Nat := 118140960795 + 5820411 * 2 ^ 59
def prefixEnd_5820411 : Nat := 4983230072969 + 3 ^ 40 * 5820411 * 2
def baseEnd_5820411 : Nat := 2988668449716332348894923

theorem tailTrace_5820411 : CollatzResearch.WordTrace tailWord_5820411 prefixEnd_5820411 2988668449716332348894923 := by
  unfold tailWord_5820411
  simp only [CollatzResearch.WordTrace]
  refine ⟨212287829316652468903781087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141525219544434979269187391 212287829316652468903781087)
  ·
    refine ⟨318431743974978703355671631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212287829316652468903781087 318431743974978703355671631)
    ·
      refine ⟨477647615962468055033507447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318431743974978703355671631 477647615962468055033507447)
      ·
        refine ⟨716471423943702082550261171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477647615962468055033507447 716471423943702082550261171)
        ·
          refine ⟨1074707135915553123825391757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716471423943702082550261171 1074707135915553123825391757)
          ·
            refine ⟨403015175968332421434521909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074707135915553123825391757 403015175968332421434521909)
            ·
              refine ⟨37782672747031164509486429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 403015175968332421434521909 37782672747031164509486429)
              ·
                refine ⟨14168502280136686691057411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37782672747031164509486429 14168502280136686691057411)
                ·
                  refine ⟨21252753420205030036586117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14168502280136686691057411 21252753420205030036586117)
                  ·
                    refine ⟨3984891266288443131859897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21252753420205030036586117 3984891266288443131859897)
                    ·
                      refine ⟨2988668449716332348894923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984891266288443131859897 2988668449716332348894923)
                      ·
                        rfl

theorem cell23_5820411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 4, 2].length) (baseStart_5820411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820411 prefixEnd_5820411 := by exact prefixLift 5820411
  have htrace : WordTrace (prefixWord ++ tailWord_5820411) baseStart_5820411 baseEnd_5820411 := by
    simpa [prefixWord, tailWord_5820411, baseEnd_5820411] using wordTrace_append hprefix tailTrace_5820411
  have hstable : (prefixWord ++ tailWord_5820411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820411).length < 2 ^ (prefixWord ++ tailWord_5820411).sum := by decide
  have hdescent : baseEnd_5820411 < baseStart_5820411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820424 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5820424 : Nat := 118140960795 + 5820424 * 2 ^ 59
def prefixEnd_5820424 : Nat := 4983230072969 + 3 ^ 40 * 5820424 * 2
def baseEnd_5820424 : Nat := 2988675124964840798032363

theorem tailTrace_5820424 : CollatzResearch.WordTrace tailWord_5820424 prefixEnd_5820424 2988675124964840798032363 := by
  unfold tailWord_5820424
  simp only [CollatzResearch.WordTrace]
  refine ⟨106144151732802686062002163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141525535643736914749336217 106144151732802686062002163)
  ·
    refine ⟨159216227599204029093003245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106144151732802686062002163 159216227599204029093003245)
    ·
      refine ⟨59706085349701510909876217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159216227599204029093003245 59706085349701510909876217)
      ·
        refine ⟨44779564012276133182407163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59706085349701510909876217 44779564012276133182407163)
        ·
          refine ⟨67169346018414199773610745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44779564012276133182407163 67169346018414199773610745)
          ·
            refine ⟨50377009513810649830208059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67169346018414199773610745 50377009513810649830208059)
            ·
              refine ⟨75565514270715974745312089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50377009513810649830208059 75565514270715974745312089)
              ·
                refine ⟨56674135703036981058984067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75565514270715974745312089 56674135703036981058984067)
                ·
                  refine ⟨85011203554555471588476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56674135703036981058984067 85011203554555471588476101)
                  ·
                    refine ⟨15939600666479150922839269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85011203554555471588476101 15939600666479150922839269)
                    ·
                      refine ⟨2988675124964840798032363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15939600666479150922839269 2988675124964840798032363)
                      ·
                        rfl

theorem cell23_5820424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5820424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820424 prefixEnd_5820424 := by exact prefixLift 5820424
  have htrace : WordTrace (prefixWord ++ tailWord_5820424) baseStart_5820424 baseEnd_5820424 := by
    simpa [prefixWord, tailWord_5820424, baseEnd_5820424] using wordTrace_append hprefix tailTrace_5820424
  have hstable : (prefixWord ++ tailWord_5820424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820424).length < 2 ^ (prefixWord ++ tailWord_5820424).sum := by decide
  have hdescent : baseEnd_5820424 < baseStart_5820424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820428 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_5820428 : Nat := 118140960795 + 5820428 * 2 ^ 59
def prefixEnd_5820428 : Nat := 4983230072969 + 3 ^ 40 * 5820428 * 2
def baseEnd_5820428 : Nat := 2988677178887458782382345

theorem tailTrace_5820428 : CollatzResearch.WordTrace tailWord_5820428 prefixEnd_5820428 2988677178887458782382345 := by
  unfold tailWord_5820428
  simp only [CollatzResearch.WordTrace]
  refine ⟨106144224678795440403574969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141525632905060587204766625 106144224678795440403574969)
  ·
    refine ⟨79608168509096580302681227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106144224678795440403574969 79608168509096580302681227)
    ·
      refine ⟨119412252763644870454021841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79608168509096580302681227 119412252763644870454021841)
      ·
        refine ⟨89559189572733652840516381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119412252763644870454021841 89559189572733652840516381)
        ·
          refine ⟨33584696089775119815193643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89559189572733652840516381 33584696089775119815193643)
          ·
            refine ⟨50377044134662679722790465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33584696089775119815193643 50377044134662679722790465)
            ·
              refine ⟨37782783100997009792092849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50377044134662679722790465 37782783100997009792092849)
              ·
                refine ⟨28337087325747757344069637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37782783100997009792092849 28337087325747757344069637)
                ·
                  refine ⟨5313203873577704502013057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28337087325747757344069637 5313203873577704502013057)
                  ·
                    refine ⟨3984902905183278376509793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313203873577704502013057 3984902905183278376509793)
                    ·
                      refine ⟨2988677178887458782382345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984902905183278376509793 2988677178887458782382345)
                      ·
                        rfl

theorem cell23_5820428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_5820428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820428 prefixEnd_5820428 := by exact prefixLift 5820428
  have htrace : WordTrace (prefixWord ++ tailWord_5820428) baseStart_5820428 baseEnd_5820428 := by
    simpa [prefixWord, tailWord_5820428, baseEnd_5820428] using wordTrace_append hprefix tailTrace_5820428
  have hstable : (prefixWord ++ tailWord_5820428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820428).length < 2 ^ (prefixWord ++ tailWord_5820428).sum := by decide
  have hdescent : baseEnd_5820428 < baseStart_5820428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820445 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5820445 : Nat := 118140960795 + 5820445 * 2 ^ 59
def prefixEnd_5820445 : Nat := 4983230072969 + 3 ^ 40 * 5820445 * 2
def baseEnd_5820445 : Nat := 2988685908058585215869767

theorem tailTrace_5820445 : CollatzResearch.WordTrace tailWord_5820445 prefixEnd_5820445 2988685908058585215869767 := by
  unfold tailWord_5820445
  simp only [CollatzResearch.WordTrace]
  refine ⟨212289069398529292710518789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141526046265686195140345859 212289069398529292710518789)
  ·
    refine ⟨39804200512224242383222273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212289069398529292710518789 39804200512224242383222273)
    ·
      refine ⟨29853150384168181787416705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39804200512224242383222273 29853150384168181787416705)
      ·
        refine ⟨22389862788126136340562529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29853150384168181787416705 22389862788126136340562529)
        ·
          refine ⟨16792397091094602255421897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389862788126136340562529 16792397091094602255421897)
          ·
            refine ⟨12594297818320951691566423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16792397091094602255421897 12594297818320951691566423)
            ·
              refine ⟨18891446727481427537349635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12594297818320951691566423 18891446727481427537349635)
              ·
                refine ⟨28337170091222141306024453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18891446727481427537349635 28337170091222141306024453)
                ·
                  refine ⟨5313219392104151494879585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28337170091222141306024453 5313219392104151494879585)
                  ·
                    refine ⟨3984914544078113621159689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313219392104151494879585 3984914544078113621159689)
                    ·
                      refine ⟨2988685908058585215869767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984914544078113621159689 2988685908058585215869767)
                      ·
                        rfl

theorem cell23_5820445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5820445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820445 prefixEnd_5820445 := by exact prefixLift 5820445
  have htrace : WordTrace (prefixWord ++ tailWord_5820445) baseStart_5820445 baseEnd_5820445 := by
    simpa [prefixWord, tailWord_5820445, baseEnd_5820445] using wordTrace_append hprefix tailTrace_5820445
  have hstable : (prefixWord ++ tailWord_5820445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820445).length < 2 ^ (prefixWord ++ tailWord_5820445).sum := by decide
  have hdescent : baseEnd_5820445 < baseStart_5820445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820451 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 5]
def baseStart_5820451 : Nat := 118140960795 + 5820451 * 2 ^ 59
def prefixEnd_5820451 : Nat := 4983230072969 + 3 ^ 40 * 5820451 * 2
def baseEnd_5820451 : Nat := 332076554326945799154971

theorem tailTrace_5820451 : CollatzResearch.WordTrace tailWord_5820451 prefixEnd_5820451 332076554326945799154971 := by
  unfold tailWord_5820451
  simp only [CollatzResearch.WordTrace]
  refine ⟨212289288236507555735237207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141526192157671703823491471 212289288236507555735237207)
  ·
    refine ⟨318433932354761333602855811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212289288236507555735237207 318433932354761333602855811)
    ·
      refine ⟨477650898532142000404283717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318433932354761333602855811 477650898532142000404283717)
      ·
        refine ⟨89559543474776625075803197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477650898532142000404283717 89559543474776625075803197)
        ·
          refine ⟨33584828803041234403426199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89559543474776625075803197 33584828803041234403426199)
          ·
            refine ⟨50377243204561851605139299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33584828803041234403426199 50377243204561851605139299)
            ·
              refine ⟨75565864806842777407708949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50377243204561851605139299 75565864806842777407708949)
              ·
                refine ⟨3542149912820755190986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75565864806842777407708949 3542149912820755190986357)
                ·
                  refine ⟨332076554326945799154971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542149912820755190986357 332076554326945799154971)
                  ·
                    rfl

theorem cell23_5820451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 5].length) (baseStart_5820451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820451 prefixEnd_5820451 := by exact prefixLift 5820451
  have htrace : WordTrace (prefixWord ++ tailWord_5820451) baseStart_5820451 baseEnd_5820451 := by
    simpa [prefixWord, tailWord_5820451, baseEnd_5820451] using wordTrace_append hprefix tailTrace_5820451
  have hstable : (prefixWord ++ tailWord_5820451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820451).length < 2 ^ (prefixWord ++ tailWord_5820451).sum := by decide
  have hdescent : baseEnd_5820451 < baseStart_5820451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820464 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_5820464 : Nat := 118140960795 + 5820464 * 2 ^ 59
def prefixEnd_5820464 : Nat := 4983230072969 + 3 ^ 40 * 5820464 * 2
def baseEnd_5820464 : Nat := 996231888063673547177393

theorem tailTrace_5820464 : CollatzResearch.WordTrace tailWord_5820464 prefixEnd_5820464 996231888063673547177393 := by
  unfold tailWord_5820464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106144881192730229477730223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141526508256973639303640297 106144881192730229477730223)
  ·
    refine ⟨159217321789095344216595335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106144881192730229477730223 159217321789095344216595335)
    ·
      refine ⟨238825982683643016324893003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159217321789095344216595335 238825982683643016324893003)
      ·
        refine ⟨358238974025464524487339505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238825982683643016324893003 358238974025464524487339505)
        ·
          refine ⟨268679230519098393365504629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358238974025464524487339505 268679230519098393365504629)
          ·
            refine ⟨25188677861165474378016059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268679230519098393365504629 25188677861165474378016059)
            ·
              refine ⟨37783016791748211567024089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25188677861165474378016059 37783016791748211567024089)
              ·
                refine ⟨28337262593811158675268067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37783016791748211567024089 28337262593811158675268067)
                ·
                  refine ⟨42505893890716738012902101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28337262593811158675268067 42505893890716738012902101)
                  ·
                    refine ⟨996231888063673547177393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42505893890716738012902101 996231888063673547177393)
                    ·
                      rfl

theorem cell23_5820464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_5820464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820464 prefixEnd_5820464 := by exact prefixLift 5820464
  have htrace : WordTrace (prefixWord ++ tailWord_5820464) baseStart_5820464 baseEnd_5820464 := by
    simpa [prefixWord, tailWord_5820464, baseEnd_5820464] using wordTrace_append hprefix tailTrace_5820464
  have hstable : (prefixWord ++ tailWord_5820464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820464).length < 2 ^ (prefixWord ++ tailWord_5820464).sum := by decide
  have hdescent : baseEnd_5820464 < baseStart_5820464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820471 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_5820471 : Nat := 118140960795 + 5820471 * 2 ^ 59
def prefixEnd_5820471 : Nat := 4983230072969 + 3 ^ 40 * 5820471 * 2
def baseEnd_5820471 : Nat := 2988699258555602114144647

theorem tailTrace_5820471 : CollatzResearch.WordTrace tailWord_5820471 prefixEnd_5820471 2988699258555602114144647 := by
  unfold tailWord_5820471
  simp only [CollatzResearch.WordTrace]
  refine ⟨212290017696435099150965267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141526678464290066100643511 212290017696435099150965267)
  ·
    refine ⟨318435026544652648726447901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212290017696435099150965267 318435026544652648726447901)
    ·
      refine ⟨119413134954244743272417963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318435026544652648726447901 119413134954244743272417963)
      ·
        refine ⟨179119702431367114908626945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119413134954244743272417963 179119702431367114908626945)
        ·
          refine ⟨134339776823525336181470209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179119702431367114908626945 134339776823525336181470209)
          ·
            refine ⟨100754832617644002136102657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134339776823525336181470209 100754832617644002136102657)
            ·
              refine ⟨75566124463233001602076993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100754832617644002136102657 75566124463233001602076993)
              ·
                refine ⟨56674593347424751201557745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75566124463233001602076993 56674593347424751201557745)
                ·
                  refine ⟨42505945010568563401168309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56674593347424751201557745 42505945010568563401168309)
                  ·
                    refine ⟨3984932344740802818859529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42505945010568563401168309 3984932344740802818859529)
                    ·
                      refine ⟨2988699258555602114144647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3984932344740802818859529 2988699258555602114144647)
                      ·
                        rfl

theorem cell23_5820471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_5820471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820471 prefixEnd_5820471 := by exact prefixLift 5820471
  have htrace : WordTrace (prefixWord ++ tailWord_5820471) baseStart_5820471 baseEnd_5820471 := by
    simpa [prefixWord, tailWord_5820471, baseEnd_5820471] using wordTrace_append hprefix tailTrace_5820471
  have hstable : (prefixWord ++ tailWord_5820471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820471).length < 2 ^ (prefixWord ++ tailWord_5820471).sum := by decide
  have hdescent : baseEnd_5820471 < baseStart_5820471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820474 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_5820474 : Nat := 118140960795 + 5820474 * 2 ^ 59
def prefixEnd_5820474 : Nat := 4983230072969 + 3 ^ 40 * 5820474 * 2
def baseEnd_5820474 : Nat := 2988700798997565602407133

theorem tailTrace_5820474 : CollatzResearch.WordTrace tailWord_5820474 prefixEnd_5820474 2988700798997565602407133 := by
  unfold tailWord_5820474
  simp only [CollatzResearch.WordTrace]
  refine ⟨53072531778856057665831119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141526751410282820442216317 53072531778856057665831119)
  ·
    refine ⟨79608797668284086498746679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53072531778856057665831119 79608797668284086498746679)
    ·
      refine ⟨119413196502426129748120019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79608797668284086498746679 119413196502426129748120019)
      ·
        refine ⟨179119794753639194622180029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119413196502426129748120019 179119794753639194622180029)
        ·
          refine ⟨67169923032614697983317511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179119794753639194622180029 67169923032614697983317511)
          ·
            refine ⟨100754884548922046974976267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67169923032614697983317511 100754884548922046974976267)
            ·
              refine ⟨151132326823383070462464401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100754884548922046974976267 151132326823383070462464401)
              ·
                refine ⟨113349245117537302846848301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151132326823383070462464401 113349245117537302846848301)
                ·
                  refine ⟨42505966919076488567568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113349245117537302846848301 42505966919076488567568113)
                  ·
                    refine ⟨31879475189307366425676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42505966919076488567568113 31879475189307366425676085)
                    ·
                      refine ⟨2988700798997565602407133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31879475189307366425676085 2988700798997565602407133)
                      ·
                        rfl

theorem cell23_5820474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_5820474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820474 prefixEnd_5820474 := by exact prefixLift 5820474
  have htrace : WordTrace (prefixWord ++ tailWord_5820474) baseStart_5820474 baseEnd_5820474 := by
    simpa [prefixWord, tailWord_5820474, baseEnd_5820474] using wordTrace_append hprefix tailTrace_5820474
  have hstable : (prefixWord ++ tailWord_5820474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820474).length < 2 ^ (prefixWord ++ tailWord_5820474).sum := by decide
  have hdescent : baseEnd_5820474 < baseStart_5820474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820481 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5820481 : Nat := 118140960795 + 5820481 * 2 ^ 59
def prefixEnd_5820481 : Nat := 4983230072969 + 3 ^ 40 * 5820481 * 2
def baseEnd_5820481 : Nat := 996234797787382358339867

theorem tailTrace_5820481 : CollatzResearch.WordTrace tailWord_5820481 prefixEnd_5820481 996234797787382358339867 := by
  unfold tailWord_5820481
  simp only [CollatzResearch.WordTrace]
  refine ⟨212290382426398870858829297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141526921617599247239219531 212290382426398870858829297)
  ·
    refine ⟨159217786819799153144121973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212290382426398870858829297 159217786819799153144121973)
    ·
      refine ⟨14926667514356170607261435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159217786819799153144121973 14926667514356170607261435)
      ·
        refine ⟨22390001271534255910892153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926667514356170607261435 22390001271534255910892153)
        ·
          refine ⟨16792500953650691933169115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22390001271534255910892153 16792500953650691933169115)
          ·
            refine ⟨25188751430476037899753673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16792500953650691933169115 25188751430476037899753673)
            ·
              refine ⟨18891563572857028424815255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25188751430476037899753673 18891563572857028424815255)
              ·
                refine ⟨28337345359285542637222883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18891563572857028424815255 28337345359285542637222883)
                ·
                  refine ⟨42506018038928313955834325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28337345359285542637222883 42506018038928313955834325)
                  ·
                    refine ⟨996234797787382358339867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42506018038928313955834325 996234797787382358339867)
                    ·
                      rfl

theorem cell23_5820481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5820481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820481 prefixEnd_5820481 := by exact prefixLift 5820481
  have htrace : WordTrace (prefixWord ++ tailWord_5820481) baseStart_5820481 baseEnd_5820481 := by
    simpa [prefixWord, tailWord_5820481, baseEnd_5820481] using wordTrace_append hprefix tailTrace_5820481
  have hstable : (prefixWord ++ tailWord_5820481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820481).length < 2 ^ (prefixWord ++ tailWord_5820481).sum := by decide
  have hdescent : baseEnd_5820481 < baseStart_5820481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820498 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_5820498 : Nat := 118140960795 + 5820498 * 2 ^ 59
def prefixEnd_5820498 : Nat := 4983230072969 + 3 ^ 40 * 5820498 * 2
def baseEnd_5820498 : Nat := 996237707511091169502341

theorem tailTrace_5820498 : CollatzResearch.WordTrace tailWord_5820498 prefixEnd_5820498 996237707511091169502341 := by
  unfold tailWord_5820498
  simp only [CollatzResearch.WordTrace]
  refine ⟨53072750616834320690549537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141527334978224855174798765 53072750616834320690549537)
  ·
    refine ⟨39804562962625740517912153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53072750616834320690549537 39804562962625740517912153)
    ·
      refine ⟨29853422221969305388434115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39804562962625740517912153 29853422221969305388434115)
      ·
        refine ⟨44780133332953958082651173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29853422221969305388434115 44780133332953958082651173)
        ·
          refine ⟨8396274999928867140497095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44780133332953958082651173 8396274999928867140497095)
          ·
            refine ⟨12594412499893300710745643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396274999928867140497095 12594412499893300710745643)
            ·
              refine ⟨18891618749839951066118465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12594412499893300710745643 18891618749839951066118465)
              ·
                refine ⟨14168714062379963299588849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18891618749839951066118465 14168714062379963299588849)
                ·
                  refine ⟨10626535546784972474691637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14168714062379963299588849 10626535546784972474691637)
                  ·
                    refine ⟨996237707511091169502341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10626535546784972474691637 996237707511091169502341)
                    ·
                      rfl

theorem cell23_5820498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_5820498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820498 prefixEnd_5820498 := by exact prefixLift 5820498
  have htrace : WordTrace (prefixWord ++ tailWord_5820498) baseStart_5820498 baseEnd_5820498 := by
    simpa [prefixWord, tailWord_5820498, baseEnd_5820498] using wordTrace_append hprefix tailTrace_5820498
  have hstable : (prefixWord ++ tailWord_5820498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820498).length < 2 ^ (prefixWord ++ tailWord_5820498).sum := by decide
  have hdescent : baseEnd_5820498 < baseStart_5820498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820501 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5820501 : Nat := 118140960795 + 5820501 * 2 ^ 59
def prefixEnd_5820501 : Nat := 4983230072969 + 3 ^ 40 * 5820501 * 2
def baseEnd_5820501 : Nat := 2988714662975236996769509

theorem tailTrace_5820501 : CollatzResearch.WordTrace tailWord_5820501 prefixEnd_5820501 2988714662975236996769509 := by
  unfold tailWord_5820501
  simp only [CollatzResearch.WordTrace]
  refine ⟨212291111886326414274557357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141527407924217609516371571 212291111886326414274557357)
  ·
    refine ⟨79609166957372405352959009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212291111886326414274557357 79609166957372405352959009)
    ·
      refine ⟨59706875218029304014719257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79609166957372405352959009 59706875218029304014719257)
      ·
        refine ⟨44780156413521978011039443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59706875218029304014719257 44780156413521978011039443)
        ·
          refine ⟨67170234620282967016559165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44780156413521978011039443 67170234620282967016559165)
          ·
            refine ⟨25188837982606112631209687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67170234620282967016559165 25188837982606112631209687)
            ·
              refine ⟨37783256973909168946814531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25188837982606112631209687 37783256973909168946814531)
              ·
                refine ⟨56674885460863753420221797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37783256973909168946814531 56674885460863753420221797)
                ·
                  refine ⟨10626541023911953766291587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56674885460863753420221797 10626541023911953766291587)
                  ·
                    refine ⟨15939811535867930649437381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10626541023911953766291587 15939811535867930649437381)
                    ·
                      refine ⟨2988714662975236996769509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15939811535867930649437381 2988714662975236996769509)
                      ·
                        rfl

theorem cell23_5820501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5820501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820501 prefixEnd_5820501 := by exact prefixLift 5820501
  have htrace : WordTrace (prefixWord ++ tailWord_5820501) baseStart_5820501 baseEnd_5820501 := by
    simpa [prefixWord, tailWord_5820501, baseEnd_5820501] using wordTrace_append hprefix tailTrace_5820501
  have hstable : (prefixWord ++ tailWord_5820501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820501).length < 2 ^ (prefixWord ++ tailWord_5820501).sum := by decide
  have hdescent : baseEnd_5820501 < baseStart_5820501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820511 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 3, 4]
def baseStart_5820511 : Nat := 118140960795 + 5820511 * 2 ^ 59
def prefixEnd_5820511 : Nat := 4983230072969 + 3 ^ 40 * 5820511 * 2
def baseEnd_5820511 : Nat := 996239932593927319214821

theorem tailTrace_5820511 : CollatzResearch.WordTrace tailWord_5820511 prefixEnd_5820511 996239932593927319214821 := by
  unfold tailWord_5820511
  simp only [CollatzResearch.WordTrace]
  refine ⟨212291476616290185982421387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141527651077526790654947591 212291476616290185982421387)
  ·
    refine ⟨318437214924435278973632081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212291476616290185982421387 318437214924435278973632081)
    ·
      refine ⟨238827911193326459230224061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318437214924435278973632081 238827911193326459230224061)
      ·
        refine ⟨89560466697497422211334023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238827911193326459230224061 89560466697497422211334023)
        ·
          refine ⟨134340700046246133317001035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89560466697497422211334023 134340700046246133317001035)
          ·
            refine ⟨201511050069369199975501553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134340700046246133317001035 201511050069369199975501553)
            ·
              refine ⟨151133287552026899981626165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201511050069369199975501553 151133287552026899981626165)
              ·
                refine ⟨14168745708002521873277453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151133287552026899981626165 14168745708002521873277453)
                ·
                  refine ⟨5313279640500945702479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14168745708002521873277453 5313279640500945702479045)
                  ·
                    refine ⟨996239932593927319214821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313279640500945702479045 996239932593927319214821)
                    ·
                      rfl

theorem cell23_5820511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_5820511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820511 prefixEnd_5820511 := by exact prefixLift 5820511
  have htrace : WordTrace (prefixWord ++ tailWord_5820511) baseStart_5820511 baseEnd_5820511 := by
    simpa [prefixWord, tailWord_5820511, baseEnd_5820511] using wordTrace_append hprefix tailTrace_5820511
  have hstable : (prefixWord ++ tailWord_5820511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820511).length < 2 ^ (prefixWord ++ tailWord_5820511).sum := by decide
  have hdescent : baseEnd_5820511 < baseStart_5820511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820521 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_5820521 : Nat := 118140960795 + 5820521 * 2 ^ 59
def prefixEnd_5820521 : Nat := 4983230072969 + 3 ^ 40 * 5820521 * 2
def baseEnd_5820521 : Nat := 2988724932588326918519417

theorem tailTrace_5820521 : CollatzResearch.WordTrace tailWord_5820521 prefixEnd_5820521 2988724932588326918519417 := by
  unfold tailWord_5820521
  simp only [CollatzResearch.WordTrace]
  refine ⟨212291841346253957690285417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141527894230835971793523611 212291841346253957690285417)
  ·
    refine ⟨159218881009690468267714063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212291841346253957690285417 159218881009690468267714063)
    ·
      refine ⟨238828321514535702401571095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159218881009690468267714063 238828321514535702401571095)
      ·
        refine ⟨358242482271803553602356643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238828321514535702401571095 358242482271803553602356643)
        ·
          refine ⟨537363723407705330403534965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358242482271803553602356643 537363723407705330403534965)
          ·
            refine ⟨50377849069472374725331403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 537363723407705330403534965 50377849069472374725331403)
            ·
              refine ⟨75566773604208562087997105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50377849069472374725331403 75566773604208562087997105)
              ·
                refine ⟨56675080203156421565997829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75566773604208562087997105 56675080203156421565997829)
                ·
                  refine ⟨10626577538091829043624593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56675080203156421565997829 10626577538091829043624593)
                  ·
                    refine ⟨7969933153568871782718445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10626577538091829043624593 7969933153568871782718445)
                    ·
                      refine ⟨2988724932588326918519417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7969933153568871782718445 2988724932588326918519417)
                      ·
                        rfl

theorem cell23_5820521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_5820521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820521 prefixEnd_5820521 := by exact prefixLift 5820521
  have htrace : WordTrace (prefixWord ++ tailWord_5820521) baseStart_5820521 baseEnd_5820521 := by
    simpa [prefixWord, tailWord_5820521, baseEnd_5820521] using wordTrace_append hprefix tailTrace_5820521
  have hstable : (prefixWord ++ tailWord_5820521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820521).length < 2 ^ (prefixWord ++ tailWord_5820521).sum := by decide
  have hdescent : baseEnd_5820521 < baseStart_5820521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_5820544 : Nat := 118140960795 + 5820544 * 2 ^ 59
def prefixEnd_5820544 : Nat := 4983230072969 + 3 ^ 40 * 5820544 * 2
def baseEnd_5820544 : Nat := 2988736742643380328531811

theorem tailTrace_5820544 : CollatzResearch.WordTrace tailWord_5820544 prefixEnd_5820544 2988736742643380328531811 := by
  unfold tailWord_5820544
  simp only [CollatzResearch.WordTrace]
  refine ⟨106146340112585316309186343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141528453483447088412248457 106146340112585316309186343)
  ·
    refine ⟨159219510168877974463779515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106146340112585316309186343 159219510168877974463779515)
    ·
      refine ⟨238829265253316961695669273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159219510168877974463779515 238829265253316961695669273)
      ·
        refine ⟨179121948939987721271751955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238829265253316961695669273 179121948939987721271751955)
        ·
          refine ⟨268682923409981581907627933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179121948939987721271751955 268682923409981581907627933)
          ·
            refine ⟨100756096278743093215360475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268682923409981581907627933 100756096278743093215360475)
            ·
              refine ⟨151134144418114639823040713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100756096278743093215360475 151134144418114639823040713)
              ·
                refine ⟨113350608313585979867280535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151134144418114639823040713 113350608313585979867280535)
                ·
                  refine ⟨170025912470378969800920803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113350608313585979867280535 170025912470378969800920803)
                  ·
                    refine ⟨255038868705568454701381205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170025912470378969800920803 255038868705568454701381205)
                    ·
                      refine ⟨2988736742643380328531811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255038868705568454701381205 2988736742643380328531811)
                      ·
                        rfl

theorem cell23_5820544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_5820544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820544 prefixEnd_5820544 := by exact prefixLift 5820544
  have htrace : WordTrace (prefixWord ++ tailWord_5820544) baseStart_5820544 baseEnd_5820544 := by
    simpa [prefixWord, tailWord_5820544, baseEnd_5820544] using wordTrace_append hprefix tailTrace_5820544
  have hstable : (prefixWord ++ tailWord_5820544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820544).length < 2 ^ (prefixWord ++ tailWord_5820544).sum := by decide
  have hdescent : baseEnd_5820544 < baseStart_5820544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820601 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_5820601 : Nat := 118140960795 + 5820601 * 2 ^ 59
def prefixEnd_5820601 : Nat := 4983230072969 + 3 ^ 40 * 5820601 * 2
def baseEnd_5820601 : Nat := 996255337013562201839683

theorem tailTrace_5820601 : CollatzResearch.WordTrace tailWord_5820601 prefixEnd_5820601 996255337013562201839683 := by
  unfold tailWord_5820601
  simp only [CollatzResearch.WordTrace]
  refine ⟨212294759185964131353197657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141529839457309420902131771 212294759185964131353197657)
  ·
    refine ⟨159221069389473098514898243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212294759185964131353197657 159221069389473098514898243)
    ·
      refine ⟨238831604084209647772347365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159221069389473098514898243 238831604084209647772347365)
      ·
        refine ⟨44780925765789308957315131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238831604084209647772347365 44780925765789308957315131)
        ·
          refine ⟨67171388648683963435972697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44780925765789308957315131 67171388648683963435972697)
          ·
            refine ⟨50378541486512972576979523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67171388648683963435972697 50378541486512972576979523)
            ·
              refine ⟨75567812229769458865469285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50378541486512972576979523 75567812229769458865469285)
              ·
                refine ⟨14168964793081773537275491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75567812229769458865469285 14168964793081773537275491)
                ·
                  refine ⟨21253447189622660305913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14168964793081773537275491 21253447189622660305913237)
                  ·
                    refine ⟨996255337013562201839683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21253447189622660305913237 996255337013562201839683)
                    ·
                      rfl

theorem cell23_5820601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_5820601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820601 prefixEnd_5820601 := by exact prefixLift 5820601
  have htrace : WordTrace (prefixWord ++ tailWord_5820601) baseStart_5820601 baseEnd_5820601 := by
    simpa [prefixWord, tailWord_5820601, baseEnd_5820601] using wordTrace_append hprefix tailTrace_5820601
  have hstable : (prefixWord ++ tailWord_5820601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820601).length < 2 ^ (prefixWord ++ tailWord_5820601).sum := by decide
  have hdescent : baseEnd_5820601 < baseStart_5820601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820618 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_5820618 : Nat := 118140960795 + 5820618 * 2 ^ 59
def prefixEnd_5820618 : Nat := 4983230072969 + 3 ^ 40 * 5820618 * 2
def baseEnd_5820618 : Nat := 996258246737271013002157

theorem tailTrace_5820618 : CollatzResearch.WordTrace tailWord_5820618 prefixEnd_5820618 996258246737271013002157 := by
  unfold tailWord_5820618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53073844806725635814141627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141530252817935028837711005 53073844806725635814141627)
  ·
    refine ⟨79610767210088453721212441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53073844806725635814141627 79610767210088453721212441)
    ·
      refine ⟨59708075407566340290909331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79610767210088453721212441 59708075407566340290909331)
      ·
        refine ⟨89562113111349510436363997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59708075407566340290909331 89562113111349510436363997)
        ·
          refine ⟨33585792416756066413636499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89562113111349510436363997 33585792416756066413636499)
          ·
            refine ⟨50378688625134099620454749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33585792416756066413636499 50378688625134099620454749)
            ·
              refine ⟨18892008234425287357670531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50378688625134099620454749 18892008234425287357670531)
              ·
                refine ⟨28338012351637931036505797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18892008234425287357670531 28338012351637931036505797)
                ·
                  refine ⟨5313377315932112069344837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28338012351637931036505797 5313377315932112069344837)
                  ·
                    refine ⟨996258246737271013002157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313377315932112069344837 996258246737271013002157)
                    ·
                      rfl

theorem cell23_5820618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_5820618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820618 prefixEnd_5820618 := by exact prefixLift 5820618
  have htrace : WordTrace (prefixWord ++ tailWord_5820618) baseStart_5820618 baseEnd_5820618 := by
    simpa [prefixWord, tailWord_5820618, baseEnd_5820618] using wordTrace_append hprefix tailTrace_5820618
  have hstable : (prefixWord ++ tailWord_5820618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820618).length < 2 ^ (prefixWord ++ tailWord_5820618).sum := by decide
  have hdescent : baseEnd_5820618 < baseStart_5820618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820625 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_5820625 : Nat := 118140960795 + 5820625 * 2 ^ 59
def prefixEnd_5820625 : Nat := 4983230072969 + 3 ^ 40 * 5820625 * 2
def baseEnd_5820625 : Nat := 2988778334576394511618939

theorem tailTrace_5820625 : CollatzResearch.WordTrace tailWord_5820625 prefixEnd_5820625 2988778334576394511618939 := by
  unfold tailWord_5820625
  simp only [CollatzResearch.WordTrace]
  refine ⟨212295634537877183452071329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141530423025251455634714219 212295634537877183452071329)
  ·
    refine ⟨159221725903407887589053497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212295634537877183452071329 159221725903407887589053497)
    ·
      refine ⟨119416294427555915691790123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159221725903407887589053497 119416294427555915691790123)
      ·
        refine ⟨179124441641333873537685185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119416294427555915691790123 179124441641333873537685185)
        ·
          refine ⟨134343331231000405153263889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179124441641333873537685185 134343331231000405153263889)
          ·
            refine ⟨100757498423250303864947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134343331231000405153263889 100757498423250303864947917)
            ·
              refine ⟨37784061908718863949355469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100757498423250303864947917 37784061908718863949355469)
              ·
                refine ⟨14169023215769573981008301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37784061908718863949355469 14169023215769573981008301)
                ·
                  refine ⟨5313383705913590242878113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14169023215769573981008301 5313383705913590242878113)
                  ·
                    refine ⟨3985037779435192682158585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313383705913590242878113 3985037779435192682158585)
                    ·
                      refine ⟨2988778334576394511618939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985037779435192682158585 2988778334576394511618939)
                      ·
                        rfl

theorem cell23_5820625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_5820625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820625 prefixEnd_5820625 := by exact prefixLift 5820625
  have htrace : WordTrace (prefixWord ++ tailWord_5820625) baseStart_5820625 baseEnd_5820625 := by
    simpa [prefixWord, tailWord_5820625, baseEnd_5820625] using wordTrace_append hprefix tailTrace_5820625
  have hstable : (prefixWord ++ tailWord_5820625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820625).length < 2 ^ (prefixWord ++ tailWord_5820625).sum := by decide
  have hdescent : baseEnd_5820625 < baseStart_5820625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820645 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5820645 : Nat := 118140960795 + 5820645 * 2 ^ 59
def prefixEnd_5820645 : Nat := 4983230072969 + 3 ^ 40 * 5820645 * 2
def baseEnd_5820645 : Nat := 2988788604189484433368847

theorem tailTrace_5820645 : CollatzResearch.WordTrace tailWord_5820645 prefixEnd_5820645 2988788604189484433368847 := by
  unfold tailWord_5820645
  simp only [CollatzResearch.WordTrace]
  refine ⟨212296363997804726867799389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141530909331869817911866259 212296363997804726867799389)
  ·
    refine ⟨79611136499176772575424771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212296363997804726867799389 79611136499176772575424771)
    ·
      refine ⟨119416704748765158863137157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79611136499176772575424771 119416704748765158863137157)
      ·
        refine ⟨22390632140393467286838217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119416704748765158863137157 22390632140393467286838217)
        ·
          refine ⟨16792974105295100465128663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22390632140393467286838217 16792974105295100465128663)
          ·
            refine ⟨25189461157942650697692995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16792974105295100465128663 25189461157942650697692995)
            ·
              refine ⟨37784191736913976046539493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25189461157942650697692995 37784191736913976046539493)
              ·
                refine ⟨7084535950671370508726155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37784191736913976046539493 7084535950671370508726155)
                ·
                  refine ⟨10626803926007055763089233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7084535950671370508726155 10626803926007055763089233)
                  ·
                    refine ⟨7970102944505291822316925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10626803926007055763089233 7970102944505291822316925)
                    ·
                      refine ⟨2988788604189484433368847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970102944505291822316925 2988788604189484433368847)
                      ·
                        rfl

theorem cell23_5820645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5820645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820645 prefixEnd_5820645 := by exact prefixLift 5820645
  have htrace : WordTrace (prefixWord ++ tailWord_5820645) baseStart_5820645 baseEnd_5820645 := by
    simpa [prefixWord, tailWord_5820645, baseEnd_5820645] using wordTrace_append hprefix tailTrace_5820645
  have hstable : (prefixWord ++ tailWord_5820645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820645).length < 2 ^ (prefixWord ++ tailWord_5820645).sum := by decide
  have hdescent : baseEnd_5820645 < baseStart_5820645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820648 : List Nat := [2, 1, 4, 1, 2, 2, 4, 7]
def baseStart_5820648 : Nat := 118140960795 + 5820648 * 2 ^ 59
def prefixEnd_5820648 : Nat := 4983230072969 + 3 ^ 40 * 5820648 * 2
def baseEnd_5820648 : Nat := 110695931282646219319679

theorem tailTrace_5820648 : CollatzResearch.WordTrace tailWord_5820648 prefixEnd_5820648 110695931282646219319679 := by
  unfold tailWord_5820648
  simp only [CollatzResearch.WordTrace]
  refine ⟨106148236708396929190079299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141530982277862572253439065 106148236708396929190079299)
  ·
    refine ⟨159222355062595393785118949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106148236708396929190079299 159222355062595393785118949)
    ·
      refine ⟨29854191574236636334709803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159222355062595393785118949 29854191574236636334709803)
      ·
        refine ⟨44781287361354954502064705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29854191574236636334709803 44781287361354954502064705)
        ·
          refine ⟨33585965521016215876548529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44781287361354954502064705 33585965521016215876548529)
          ·
            refine ⟨25189474140762161907411397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33585965521016215876548529 25189474140762161907411397)
            ·
              refine ⟨4723026401392905357639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25189474140762161907411397 4723026401392905357639637)
              ·
                refine ⟨110695931282646219319679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4723026401392905357639637 110695931282646219319679)
                ·
                  rfl

theorem cell23_5820648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 7].length) (baseStart_5820648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820648 prefixEnd_5820648 := by exact prefixLift 5820648
  have htrace : WordTrace (prefixWord ++ tailWord_5820648) baseStart_5820648 baseEnd_5820648 := by
    simpa [prefixWord, tailWord_5820648, baseEnd_5820648] using wordTrace_append hprefix tailTrace_5820648
  have hstable : (prefixWord ++ tailWord_5820648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820648).length < 2 ^ (prefixWord ++ tailWord_5820648).sum := by decide
  have hdescent : baseEnd_5820648 < baseStart_5820648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820671 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_5820671 : Nat := 118140960795 + 5820671 * 2 ^ 59
def prefixEnd_5820671 : Nat := 4983230072969 + 3 ^ 40 * 5820671 * 2
def baseEnd_5820671 : Nat := 2988801954686501331643727

theorem tailTrace_5820671 : CollatzResearch.WordTrace tailWord_5820671 prefixEnd_5820671 2988801954686501331643727 := by
  unfold tailWord_5820671
  simp only [CollatzResearch.WordTrace]
  refine ⟨212297312295710533308245867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141531541530473688872163911 212297312295710533308245867)
  ·
    refine ⟨318445968443565799962368801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212297312295710533308245867 318445968443565799962368801)
    ·
      refine ⟨238834476332674349971776601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318445968443565799962368801 238834476332674349971776601)
      ·
        refine ⟨179125857249505762478832451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238834476332674349971776601 179125857249505762478832451)
        ·
          refine ⟨268688785874258643718248677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179125857249505762478832451 268688785874258643718248677)
          ·
            refine ⟨50379147351423495697171627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268688785874258643718248677 50379147351423495697171627)
            ·
              refine ⟨75568721027135243545757441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50379147351423495697171627 75568721027135243545757441)
              ·
                refine ⟨56676540770351432659318081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75568721027135243545757441 56676540770351432659318081)
                ·
                  refine ⟨42507405577763574494488561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56676540770351432659318081 42507405577763574494488561)
                  ·
                    refine ⟨31880554183322680870866421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42507405577763574494488561 31880554183322680870866421)
                    ·
                      refine ⟨2988801954686501331643727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31880554183322680870866421 2988801954686501331643727)
                      ·
                        rfl

theorem cell23_5820671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_5820671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820671 prefixEnd_5820671 := by exact prefixLift 5820671
  have htrace : WordTrace (prefixWord ++ tailWord_5820671) baseStart_5820671 baseEnd_5820671 := by
    simpa [prefixWord, tailWord_5820671, baseEnd_5820671] using wordTrace_append hprefix tailTrace_5820671
  have hstable : (prefixWord ++ tailWord_5820671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820671).length < 2 ^ (prefixWord ++ tailWord_5820671).sum := by decide
  have hdescent : baseEnd_5820671 < baseStart_5820671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820675 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 3]
def baseStart_5820675 : Nat := 118140960795 + 5820675 * 2 ^ 59
def prefixEnd_5820675 : Nat := 4983230072969 + 3 ^ 40 * 5820675 * 2
def baseEnd_5820675 : Nat := 2988804008609119315993709

theorem tailTrace_5820675 : CollatzResearch.WordTrace tailWord_5820675 prefixEnd_5820675 2988804008609119315993709 := by
  unfold tailWord_5820675
  simp only [CollatzResearch.WordTrace]
  refine ⟨212297458187696041991391479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141531638791797361327594319 212297458187696041991391479)
  ·
    refine ⟨318446187281544062987087219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212297458187696041991391479 318446187281544062987087219)
    ·
      refine ⟨477669280922316094480630829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318446187281544062987087219 477669280922316094480630829)
      ·
        refine ⟨179125980345868535430236561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477669280922316094480630829 179125980345868535430236561)
        ·
          refine ⟨134344485259401401572677421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179125980345868535430236561 134344485259401401572677421)
          ·
            refine ⟨50379181972275525589754033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134344485259401401572677421 50379181972275525589754033)
            ·
              refine ⟨37784386479206644192315525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50379181972275525589754033 37784386479206644192315525)
              ·
                refine ⟨7084572464851245786059161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37784386479206644192315525 7084572464851245786059161)
                ·
                  refine ⟨5313429348638434339544371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7084572464851245786059161 5313429348638434339544371)
                  ·
                    refine ⟨7970144022957651509316557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313429348638434339544371 7970144022957651509316557)
                    ·
                      refine ⟨2988804008609119315993709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970144022957651509316557 2988804008609119315993709)
                      ·
                        rfl

theorem cell23_5820675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_5820675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820675 prefixEnd_5820675 := by exact prefixLift 5820675
  have htrace : WordTrace (prefixWord ++ tailWord_5820675) baseStart_5820675 baseEnd_5820675 := by
    simpa [prefixWord, tailWord_5820675, baseEnd_5820675] using wordTrace_append hprefix tailTrace_5820675
  have hstable : (prefixWord ++ tailWord_5820675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820675).length < 2 ^ (prefixWord ++ tailWord_5820675).sum := by decide
  have hdescent : baseEnd_5820675 < baseStart_5820675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820676 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5820676 : Nat := 118140960795 + 5820676 * 2 ^ 59
def prefixEnd_5820676 : Nat := 4983230072969 + 3 ^ 40 * 5820676 * 2
def baseEnd_5820676 : Nat := 2988804522089773812081205

theorem tailTrace_5820676 : CollatzResearch.WordTrace tailWord_5820676 prefixEnd_5820676 2988804522089773812081205 := by
  unfold tailWord_5820676
  simp only [CollatzResearch.WordTrace]
  refine ⟨106148747330346209581088941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141531663107128279441451921 106148747330346209581088941)
  ·
    refine ⟨39805780248879828592908353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106148747330346209581088941 39805780248879828592908353)
    ·
      refine ⟨29854335186659871444681265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39805780248879828592908353 29854335186659871444681265)
      ·
        refine ⟨22390751389994903583510949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29854335186659871444681265 22390751389994903583510949)
        ·
          refine ⟨4198265885624044421908303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22390751389994903583510949 4198265885624044421908303)
          ·
            refine ⟨6297398828436066632862455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198265885624044421908303 6297398828436066632862455)
            ·
              refine ⟨9446098242654099949293683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297398828436066632862455 9446098242654099949293683)
              ·
                refine ⟨14169147363981149923940525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9446098242654099949293683 14169147363981149923940525)
                ·
                  refine ⟨5313430261492931221477697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14169147363981149923940525 5313430261492931221477697)
                  ·
                    refine ⟨3985072696119698416108273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313430261492931221477697 3985072696119698416108273)
                    ·
                      refine ⟨2988804522089773812081205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985072696119698416108273 2988804522089773812081205)
                      ·
                        rfl

theorem cell23_5820676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5820676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820676 prefixEnd_5820676 := by exact prefixLift 5820676
  have htrace : WordTrace (prefixWord ++ tailWord_5820676) baseStart_5820676 baseEnd_5820676 := by
    simpa [prefixWord, tailWord_5820676, baseEnd_5820676] using wordTrace_append hprefix tailTrace_5820676
  have hstable : (prefixWord ++ tailWord_5820676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820676).length < 2 ^ (prefixWord ++ tailWord_5820676).sum := by decide
  have hdescent : baseEnd_5820676 < baseStart_5820676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820691 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 6]
def baseStart_5820691 : Nat := 118140960795 + 5820691 * 2 ^ 59
def prefixEnd_5820691 : Nat := 4983230072969 + 3 ^ 40 * 5820691 * 2
def baseEnd_5820691 : Nat := 996270741433197084464545

theorem tailTrace_5820691 : CollatzResearch.WordTrace tailWord_5820691 prefixEnd_5820691 996270741433197084464545 := by
  unfold tailWord_5820691
  simp only [CollatzResearch.WordTrace]
  refine ⟨212298041755638076723973927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141532027837092051149315951 212298041755638076723973927)
  ·
    refine ⟨318447062633457115085960891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212298041755638076723973927 318447062633457115085960891)
    ·
      refine ⟨477670593950185672628941337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318447062633457115085960891 477670593950185672628941337)
      ·
        refine ⟨358252945462639254471706003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477670593950185672628941337 358252945462639254471706003)
        ·
          refine ⟨537379418193958881707559005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358252945462639254471706003 537379418193958881707559005)
          ·
            refine ⟨201517281822734580640334627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537379418193958881707559005 201517281822734580640334627)
            ·
              refine ⟨302275922734101870960501941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201517281822734580640334627 302275922734101870960501941)
              ·
                refine ⟨28338367756322050402547057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302275922734101870960501941 28338367756322050402547057)
                ·
                  refine ⟨21253775817241537801910293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28338367756322050402547057 21253775817241537801910293)
                  ·
                    refine ⟨996270741433197084464545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21253775817241537801910293 996270741433197084464545)
                    ·
                      rfl

theorem cell23_5820691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_5820691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820691 prefixEnd_5820691 := by exact prefixLift 5820691
  have htrace : WordTrace (prefixWord ++ tailWord_5820691) baseStart_5820691 baseEnd_5820691 := by
    simpa [prefixWord, tailWord_5820691, baseEnd_5820691] using wordTrace_append hprefix tailTrace_5820691
  have hstable : (prefixWord ++ tailWord_5820691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820691).length < 2 ^ (prefixWord ++ tailWord_5820691).sum := by decide
  have hdescent : baseEnd_5820691 < baseStart_5820691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820741 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_5820741 : Nat := 118140960795 + 5820741 * 2 ^ 59
def prefixEnd_5820741 : Nat := 4983230072969 + 3 ^ 40 * 5820741 * 2
def baseEnd_5820741 : Nat := 2988837898332316057768405

theorem tailTrace_5820741 : CollatzResearch.WordTrace tailWord_5820741 prefixEnd_5820741 2988837898332316057768405 := by
  unfold tailWord_5820741
  simp only [CollatzResearch.WordTrace]
  refine ⟨212299865405456935263294077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141533243603637956842196051 212299865405456935263294077)
  ·
    refine ⟨79612449527046350723735279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212299865405456935263294077 79612449527046350723735279)
    ·
      refine ⟨119418674290569526085602919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79612449527046350723735279 119418674290569526085602919)
      ·
        refine ⟨179128011435854289128404379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119418674290569526085602919 179128011435854289128404379)
        ·
          refine ⟨268692017153781433692606569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179128011435854289128404379 268692017153781433692606569)
          ·
            refine ⟨201519012865336075269454927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268692017153781433692606569 201519012865336075269454927)
            ·
              refine ⟨302278519298004112904182391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201519012865336075269454927 302278519298004112904182391)
              ·
                refine ⟨453417778947006169356273587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302278519298004112904182391 453417778947006169356273587)
                ·
                  refine ⟨680126668420509254034410381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453417778947006169356273587 680126668420509254034410381)
                  ·
                    refine ⟨255047500657690970262903893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680126668420509254034410381 255047500657690970262903893)
                    ·
                      refine ⟨2988837898332316057768405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255047500657690970262903893 2988837898332316057768405)
                      ·
                        rfl

theorem cell23_5820741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_5820741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820741 prefixEnd_5820741 := by exact prefixLift 5820741
  have htrace : WordTrace (prefixWord ++ tailWord_5820741) baseStart_5820741 baseEnd_5820741 := by
    simpa [prefixWord, tailWord_5820741, baseEnd_5820741] using wordTrace_append hprefix tailTrace_5820741
  have hstable : (prefixWord ++ tailWord_5820741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820741).length < 2 ^ (prefixWord ++ tailWord_5820741).sum := by decide
  have hdescent : baseEnd_5820741 < baseStart_5820741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820825 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_5820825 : Nat := 118140960795 + 5820825 * 2 ^ 59
def prefixEnd_5820825 : Nat := 4983230072969 + 3 ^ 40 * 5820825 * 2
def baseEnd_5820825 : Nat := 2988881030707293729118019

theorem tailTrace_5820825 : CollatzResearch.WordTrace tailWord_5820825 prefixEnd_5820825 2988881030707293729118019 := by
  unfold tailWord_5820825
  simp only [CollatzResearch.WordTrace]
  refine ⟨212302929137152617609351929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141535286091435078406234619 212302929137152617609351929)
  ·
    refine ⟨159227196852864463207013947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212302929137152617609351929 159227196852864463207013947)
    ·
      refine ⟨238840795279296694810520921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159227196852864463207013947 238840795279296694810520921)
      ·
        refine ⟨179130596459472521107890691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238840795279296694810520921 179130596459472521107890691)
        ·
          refine ⟨268695894689208781661836037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179130596459472521107890691 268695894689208781661836037)
          ·
            refine ⟨50380480254226646561594257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268695894689208781661836037 50380480254226646561594257)
            ·
              refine ⟨37785360190669984921195693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50380480254226646561594257 37785360190669984921195693)
              ·
                refine ⟨14169510071501244345448385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37785360190669984921195693 14169510071501244345448385)
                ·
                  refine ⟨10627132553625933259086289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14169510071501244345448385 10627132553625933259086289)
                  ·
                    refine ⟨7970349415219449944314717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10627132553625933259086289 7970349415219449944314717)
                    ·
                      refine ⟨2988881030707293729118019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970349415219449944314717 2988881030707293729118019)
                      ·
                        rfl

theorem cell23_5820825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_5820825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820825 prefixEnd_5820825 := by exact prefixLift 5820825
  have htrace : WordTrace (prefixWord ++ tailWord_5820825) baseStart_5820825 baseEnd_5820825 := by
    simpa [prefixWord, tailWord_5820825, baseEnd_5820825] using wordTrace_append hprefix tailTrace_5820825
  have hstable : (prefixWord ++ tailWord_5820825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820825).length < 2 ^ (prefixWord ++ tailWord_5820825).sum := by decide
  have hdescent : baseEnd_5820825 < baseStart_5820825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820862 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_5820862 : Nat := 118140960795 + 5820862 * 2 ^ 59
def prefixEnd_5820862 : Nat := 4983230072969 + 3 ^ 40 * 5820862 * 2
def baseEnd_5820862 : Nat := 332100003276834453817261

theorem tailTrace_5820862 : CollatzResearch.WordTrace tailWord_5820862 prefixEnd_5820862 332100003276834453817261 := by
  unfold tailWord_5820862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538034829752321616056105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141536185758679048618965893 26538034829752321616056105)
  ·
    refine ⟨19903526122314241212042079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26538034829752321616056105 19903526122314241212042079)
    ·
      refine ⟨29855289183471361818063119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19903526122314241212042079 29855289183471361818063119)
      ·
        refine ⟨44782933775207042727094679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29855289183471361818063119 44782933775207042727094679)
        ·
          refine ⟨67174400662810564090642019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44782933775207042727094679 67174400662810564090642019)
          ·
            refine ⟨100761600994215846135963029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67174400662810564090642019 100761600994215846135963029)
            ·
              refine ⟨4723200046603867787623267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100761600994215846135963029 4723200046603867787623267)
              ·
                refine ⟨7084800069905801681434901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723200046603867787623267 7084800069905801681434901)
                ·
                  refine ⟨332100003276834453817261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7084800069905801681434901 332100003276834453817261)
                  ·
                    rfl

theorem cell23_5820862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_5820862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820862 prefixEnd_5820862 := by exact prefixLift 5820862
  have htrace : WordTrace (prefixWord ++ tailWord_5820862) baseStart_5820862 baseEnd_5820862 := by
    simpa [prefixWord, tailWord_5820862, baseEnd_5820862] using wordTrace_append hprefix tailTrace_5820862
  have hstable : (prefixWord ++ tailWord_5820862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820862).length < 2 ^ (prefixWord ++ tailWord_5820862).sum := by decide
  have hdescent : baseEnd_5820862 < baseStart_5820862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820889 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 1, 1, 3]
def baseStart_5820889 : Nat := 118140960795 + 5820889 * 2 ^ 59
def prefixEnd_5820889 : Nat := 4983230072969 + 3 ^ 40 * 5820889 * 2
def baseEnd_5820889 : Nat := 2988913893469181478717725

theorem tailTrace_5820889 : CollatzResearch.WordTrace tailWord_5820889 prefixEnd_5820889 2988913893469181478717725 := by
  unfold tailWord_5820889
  simp only [CollatzResearch.WordTrace]
  refine ⟨212305263408920756539681721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141536842272613837693121147 212305263408920756539681721)
  ·
    refine ⟨159228947556690567404761291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212305263408920756539681721 159228947556690567404761291)
    ·
      refine ⟨238843421335035851107141937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159228947556690567404761291 238843421335035851107141937)
      ·
        refine ⟨179132566001276888330356453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238843421335035851107141937 179132566001276888330356453)
        ·
          refine ⟨33587356125239416561941835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179132566001276888330356453 33587356125239416561941835)
          ·
            refine ⟨50381034187859124842912753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33587356125239416561941835 50381034187859124842912753)
            ·
              refine ⟨37785775640894343632184565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50381034187859124842912753 37785775640894343632184565)
              ·
                refine ⟨3542416466333844715517303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37785775640894343632184565 3542416466333844715517303)
                ·
                  refine ⟨5313624699500767073275955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542416466333844715517303 5313624699500767073275955)
                  ·
                    refine ⟨7970437049251150609913933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313624699500767073275955 7970437049251150609913933)
                    ·
                      refine ⟨2988913893469181478717725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970437049251150609913933 2988913893469181478717725)
                      ·
                        rfl

theorem cell23_5820889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_5820889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820889 prefixEnd_5820889 := by exact prefixLift 5820889
  have htrace : WordTrace (prefixWord ++ tailWord_5820889) baseStart_5820889 baseEnd_5820889 := by
    simpa [prefixWord, tailWord_5820889, baseEnd_5820889] using wordTrace_append hprefix tailTrace_5820889
  have hstable : (prefixWord ++ tailWord_5820889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820889).length < 2 ^ (prefixWord ++ tailWord_5820889).sum := by decide
  have hdescent : baseEnd_5820889 < baseStart_5820889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820906 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_5820906 : Nat := 118140960795 + 5820906 * 2 ^ 59
def prefixEnd_5820906 : Nat := 4983230072969 + 3 ^ 40 * 5820906 * 2
def baseEnd_5820906 : Nat := 2988922622640307912205147

theorem tailTrace_5820906 : CollatzResearch.WordTrace tailWord_5820906 prefixEnd_5820906 2988922622640307912205147 := by
  unfold tailWord_5820906
  simp only [CollatzResearch.WordTrace]
  refine ⟨53076470862464792110762643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141537255633239445628700381 53076470862464792110762643)
  ·
    refine ⟨79614706293697188166143965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53076470862464792110762643 79614706293697188166143965)
    ·
      refine ⟨29855514860136445562303987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79614706293697188166143965 29855514860136445562303987)
      ·
        refine ⟨44783272290204668343455981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29855514860136445562303987 44783272290204668343455981)
        ·
          refine ⟨16793727108826750628795993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44783272290204668343455981 16793727108826750628795993)
          ·
            refine ⟨12595295331620062971596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16793727108826750628795993 12595295331620062971596995)
            ·
              refine ⟨18892942997430094457395493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12595295331620062971596995 18892942997430094457395493)
              ·
                refine ⟨3542426812018142710761655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18892942997430094457395493 3542426812018142710761655)
                ·
                  refine ⟨5313640218027214066142483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542426812018142710761655 5313640218027214066142483)
                  ·
                    refine ⟨7970460327040821099213725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5313640218027214066142483 7970460327040821099213725)
                    ·
                      refine ⟨2988922622640307912205147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970460327040821099213725 2988922622640307912205147)
                      ·
                        rfl

theorem cell23_5820906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_5820906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820906 prefixEnd_5820906 := by exact prefixLift 5820906
  have htrace : WordTrace (prefixWord ++ tailWord_5820906) baseStart_5820906 baseEnd_5820906 := by
    simpa [prefixWord, tailWord_5820906, baseEnd_5820906] using wordTrace_append hprefix tailTrace_5820906
  have hstable : (prefixWord ++ tailWord_5820906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820906).length < 2 ^ (prefixWord ++ tailWord_5820906).sum := by decide
  have hdescent : baseEnd_5820906 < baseStart_5820906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820915 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3]
def baseStart_5820915 : Nat := 118140960795 + 5820915 * 2 ^ 59
def prefixEnd_5820915 : Nat := 4983230072969 + 3 ^ 40 * 5820915 * 2
def baseEnd_5820915 : Nat := 2988927243966198376992605

theorem tailTrace_5820915 : CollatzResearch.WordTrace tailWord_5820915 prefixEnd_5820915 2988927243966198376992605 := by
  unfold tailWord_5820915
  simp only [CollatzResearch.WordTrace]
  refine ⟨212306211706826562980128199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141537474471217708653418799 212306211706826562980128199)
  ·
    refine ⟨318459317560239844470192299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212306211706826562980128199 318459317560239844470192299)
    ·
      refine ⟨477688976340359766705288449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318459317560239844470192299 477688976340359766705288449)
      ·
        refine ⟨358266732255269825028966337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477688976340359766705288449 358266732255269825028966337)
        ·
          refine ⟨268700049191452368771724753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358266732255269825028966337 268700049191452368771724753)
          ·
            refine ⟨201525036893589276578793565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268700049191452368771724753 201525036893589276578793565)
            ·
              refine ⟨75571888835095978717047587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201525036893589276578793565 75571888835095978717047587)
              ·
                refine ⟨113357833252643968075571381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75571888835095978717047587 113357833252643968075571381)
                ·
                  refine ⟨10627296867435372007084817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113357833252643968075571381 10627296867435372007084817)
                  ·
                    refine ⟨7970472650576529005313613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10627296867435372007084817 7970472650576529005313613)
                    ·
                      refine ⟨2988927243966198376992605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970472650576529005313613 2988927243966198376992605)
                      ·
                        rfl

theorem cell23_5820915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_5820915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820915 prefixEnd_5820915 := by exact prefixLift 5820915
  have htrace : WordTrace (prefixWord ++ tailWord_5820915) baseStart_5820915 baseEnd_5820915 := by
    simpa [prefixWord, tailWord_5820915, baseEnd_5820915] using wordTrace_append hprefix tailTrace_5820915
  have hstable : (prefixWord ++ tailWord_5820915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820915).length < 2 ^ (prefixWord ++ tailWord_5820915).sum := by decide
  have hdescent : baseEnd_5820915 < baseStart_5820915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820928 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_5820928 : Nat := 118140960795 + 5820928 * 2 ^ 59
def prefixEnd_5820928 : Nat := 4983230072969 + 3 ^ 40 * 5820928 * 2
def baseEnd_5820928 : Nat := 2988933919214706826130045

theorem tailTrace_5820928 : CollatzResearch.WordTrace tailWord_5820928 prefixEnd_5820928 2988933919214706826130045 := by
  unfold tailWord_5820928
  simp only [CollatzResearch.WordTrace]
  refine ⟨106153342927889733100175719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141537790570519644133567625 106153342927889733100175719)
  ·
    refine ⟨159230014391834599650263579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106153342927889733100175719 159230014391834599650263579)
    ·
      refine ⟨238845021587751899475395369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159230014391834599650263579 238845021587751899475395369)
      ·
        refine ⟨179133766190813924606546527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238845021587751899475395369 179133766190813924606546527)
        ·
          refine ⟨268700649286220886909819791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179133766190813924606546527 268700649286220886909819791)
          ·
            refine ⟨403050973929331330364729687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268700649286220886909819791 403050973929331330364729687)
            ·
              refine ⟨604576460893996995547094531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403050973929331330364729687 604576460893996995547094531)
              ·
                refine ⟨906864691340995493320641797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604576460893996995547094531 906864691340995493320641797)
                ·
                  refine ⟨170037129626436654997620337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906864691340995493320641797 170037129626436654997620337)
                  ·
                    refine ⟨127527847219827491248215253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170037129626436654997620337 127527847219827491248215253)
                    ·
                      refine ⟨2988933919214706826130045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127527847219827491248215253 2988933919214706826130045)
                      ·
                        rfl

theorem cell23_5820928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_5820928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820928 prefixEnd_5820928 := by exact prefixLift 5820928
  have htrace : WordTrace (prefixWord ++ tailWord_5820928) baseStart_5820928 baseEnd_5820928 := by
    simpa [prefixWord, tailWord_5820928, baseEnd_5820928] using wordTrace_append hprefix tailTrace_5820928
  have hstable : (prefixWord ++ tailWord_5820928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820928).length < 2 ^ (prefixWord ++ tailWord_5820928).sum := by decide
  have hdescent : baseEnd_5820928 < baseStart_5820928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820929 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_5820929 : Nat := 118140960795 + 5820929 * 2 ^ 59
def prefixEnd_5820929 : Nat := 4983230072969 + 3 ^ 40 * 5820929 * 2
def baseEnd_5820929 : Nat := 2988934432695361322217541

theorem tailTrace_5820929 : CollatzResearch.WordTrace tailWord_5820929 prefixEnd_5820929 2988934432695361322217541 := by
  unfold tailWord_5820929
  simp only [CollatzResearch.WordTrace]
  refine ⟨212306722328775843371137841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141537814885850562247425227 212306722328775843371137841)
  ·
    refine ⟨159230041746581882528353381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212306722328775843371137841 159230041746581882528353381)
    ·
      refine ⟨29855632827484102974066259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159230041746581882528353381 29855632827484102974066259)
      ·
        refine ⟨44783449241226154461099389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29855632827484102974066259 44783449241226154461099389)
        ·
          refine ⟨16793793465459807922912271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44783449241226154461099389 16793793465459807922912271)
          ·
            refine ⟨25190690198189711884368407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16793793465459807922912271 25190690198189711884368407)
            ·
              refine ⟨37786035297284567826552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25190690198189711884368407 37786035297284567826552611)
              ·
                refine ⟨56679052945926851739828917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37786035297284567826552611 56679052945926851739828917)
                ·
                  refine ⟨5313661213680642350608961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56679052945926851739828917 5313661213680642350608961)
                  ·
                    refine ⟨3985245910260481762956721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313661213680642350608961 3985245910260481762956721)
                    ·
                      refine ⟨2988934432695361322217541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985245910260481762956721 2988934432695361322217541)
                      ·
                        rfl

theorem cell23_5820929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_5820929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820929 prefixEnd_5820929 := by exact prefixLift 5820929
  have htrace : WordTrace (prefixWord ++ tailWord_5820929) baseStart_5820929 baseEnd_5820929 := by
    simpa [prefixWord, tailWord_5820929, baseEnd_5820929] using wordTrace_append hprefix tailTrace_5820929
  have hstable : (prefixWord ++ tailWord_5820929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820929).length < 2 ^ (prefixWord ++ tailWord_5820929).sum := by decide
  have hdescent : baseEnd_5820929 < baseStart_5820929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820942 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5820942 : Nat := 118140960795 + 5820942 * 2 ^ 59
def prefixEnd_5820942 : Nat := 4983230072969 + 3 ^ 40 * 5820942 * 2
def baseEnd_5820942 : Nat := 2988941107943869771354981

theorem tailTrace_5820942 : CollatzResearch.WordTrace tailWord_5820942 prefixEnd_5820942 2988941107943869771354981 := by
  unfold tailWord_5820942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538399559716093323920135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141538130985152497727574053 26538399559716093323920135)
  ·
    refine ⟨39807599339574139985880203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26538399559716093323920135 39807599339574139985880203)
    ·
      refine ⟨59711399009361209978820305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39807599339574139985880203 59711399009361209978820305)
      ·
        refine ⟨44783549257020907484115229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59711399009361209978820305 44783549257020907484115229)
        ·
          refine ⟨16793830971382840306543211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44783549257020907484115229 16793830971382840306543211)
          ·
            refine ⟨25190746457074260459814817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16793830971382840306543211 25190746457074260459814817)
            ·
              refine ⟨18893059842805695344861113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25190746457074260459814817 18893059842805695344861113)
              ·
                refine ⟨14169794882104271508645835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18893059842805695344861113 14169794882104271508645835)
                ·
                  refine ⟨21254692323156407262968753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14169794882104271508645835 21254692323156407262968753)
                  ·
                    refine ⟨15941019242367305447226565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21254692323156407262968753 15941019242367305447226565)
                    ·
                      refine ⟨2988941107943869771354981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15941019242367305447226565 2988941107943869771354981)
                      ·
                        rfl

theorem cell23_5820942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5820942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820942 prefixEnd_5820942 := by exact prefixLift 5820942
  have htrace : WordTrace (prefixWord ++ tailWord_5820942) baseStart_5820942 baseEnd_5820942 := by
    simpa [prefixWord, tailWord_5820942, baseEnd_5820942] using wordTrace_append hprefix tailTrace_5820942
  have hstable : (prefixWord ++ tailWord_5820942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820942).length < 2 ^ (prefixWord ++ tailWord_5820942).sum := by decide
  have hdescent : baseEnd_5820942 < baseStart_5820942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820945 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_5820945 : Nat := 118140960795 + 5820945 * 2 ^ 59
def prefixEnd_5820945 : Nat := 4983230072969 + 3 ^ 40 * 5820945 * 2
def baseEnd_5820945 : Nat := 2988942648385833259617467

theorem tailTrace_5820945 : CollatzResearch.WordTrace tailWord_5820945 prefixEnd_5820945 2988942648385833259617467 := by
  unfold tailWord_5820945
  simp only [CollatzResearch.WordTrace]
  refine ⟨212307305896717878103720289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141538203931145252069146859 212307305896717878103720289)
  ·
    refine ⟨159230479422538408577790217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212307305896717878103720289 159230479422538408577790217)
    ·
      refine ⟨119422859566903806433342663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159230479422538408577790217 119422859566903806433342663)
      ·
        refine ⟨179134289350355709650013995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119422859566903806433342663 179134289350355709650013995)
        ·
          refine ⟨268701434025533564475020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179134289350355709650013995 268701434025533564475020993)
          ·
            refine ⟨201526075519150173356265745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268701434025533564475020993 201526075519150173356265745)
            ·
              refine ⟨151144556639362630017199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201526075519150173356265745 151144556639362630017199309)
              ·
                refine ⟨56679208739760986256449741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151144556639362630017199309 56679208739760986256449741)
                ·
                  refine ⟨21254703277410369846168653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56679208739760986256449741 21254703277410369846168653)
                  ·
                    refine ⟨7970513729028888692313245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21254703277410369846168653 7970513729028888692313245)
                    ·
                      refine ⟨2988942648385833259617467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970513729028888692313245 2988942648385833259617467)
                      ·
                        rfl

theorem cell23_5820945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_5820945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820945 prefixEnd_5820945 := by exact prefixLift 5820945
  have htrace : WordTrace (prefixWord ++ tailWord_5820945) baseStart_5820945 baseEnd_5820945 := by
    simpa [prefixWord, tailWord_5820945, baseEnd_5820945] using wordTrace_append hprefix tailTrace_5820945
  have hstable : (prefixWord ++ tailWord_5820945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820945).length < 2 ^ (prefixWord ++ tailWord_5820945).sum := by decide
  have hdescent : baseEnd_5820945 < baseStart_5820945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_5820972 : Nat := 118140960795 + 5820972 * 2 ^ 59
def prefixEnd_5820972 : Nat := 4983230072969 + 3 ^ 40 * 5820972 * 2
def baseEnd_5820972 : Nat := 2988956512363504653979843

theorem tailTrace_5820972 : CollatzResearch.WordTrace tailWord_5820972 prefixEnd_5820972 2988956512363504653979843 := by
  unfold tailWord_5820972
  simp only [CollatzResearch.WordTrace]
  refine ⟨106154145333810030857476585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141538860445080041143302113 106154145333810030857476585)
  ·
    refine ⟨79615609000357523143107439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106154145333810030857476585 79615609000357523143107439)
    ·
      refine ⟨119423413500536284714661159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79615609000357523143107439 119423413500536284714661159)
      ·
        refine ⟨179135120250804427071991739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119423413500536284714661159 179135120250804427071991739)
        ·
          refine ⟨268702680376206640607987609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179135120250804427071991739 268702680376206640607987609)
          ·
            refine ⟨201527010282154980455990707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268702680376206640607987609 201527010282154980455990707)
            ·
              refine ⟨302290515423232470683986061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201527010282154980455990707 302290515423232470683986061)
              ·
                refine ⟨113358943283712176506494773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302290515423232470683986061 113358943283712176506494773)
                ·
                  refine ⟨10627400932848016547483885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113358943283712176506494773 10627400932848016547483885)
                  ·
                    refine ⟨3985275349818006205306457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10627400932848016547483885 3985275349818006205306457)
                    ·
                      refine ⟨2988956512363504653979843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985275349818006205306457 2988956512363504653979843)
                      ·
                        rfl

theorem cell23_5820972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_5820972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820972 prefixEnd_5820972 := by exact prefixLift 5820972
  have htrace : WordTrace (prefixWord ++ tailWord_5820972) baseStart_5820972 baseEnd_5820972 := by
    simpa [prefixWord, tailWord_5820972, baseEnd_5820972] using wordTrace_append hprefix tailTrace_5820972
  have hstable : (prefixWord ++ tailWord_5820972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820972).length < 2 ^ (prefixWord ++ tailWord_5820972).sum := by decide
  have hdescent : baseEnd_5820972 < baseStart_5820972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5820973 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5820973 : Nat := 118140960795 + 5820973 * 2 ^ 59
def prefixEnd_5820973 : Nat := 4983230072969 + 3 ^ 40 * 5820973 * 2
def baseEnd_5820973 : Nat := 996319008614719716689113

theorem tailTrace_5820973 : CollatzResearch.WordTrace tailWord_5820973 prefixEnd_5820973 996319008614719716689113 := by
  unfold tailWord_5820973
  simp only [CollatzResearch.WordTrace]
  refine ⟨212308327140616438885739573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141538884760410959257159715 212308327140616438885739573)
  ·
    refine ⟨19903905669432791145538085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212308327140616438885739573 19903905669432791145538085)
    ·
      refine ⟨3731982313018648339788391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19903905669432791145538085 3731982313018648339788391)
      ·
        refine ⟨5597973469527972509682587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731982313018648339788391 5597973469527972509682587)
        ·
          refine ⟨8396960204291958764523881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5597973469527972509682587 8396960204291958764523881)
          ·
            refine ⟨6297720153218969073392911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8396960204291958764523881 6297720153218969073392911)
            ·
              refine ⟨9446580229828453610089367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297720153218969073392911 9446580229828453610089367)
              ·
                refine ⟨14169870344742680415134051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9446580229828453610089367 14169870344742680415134051)
                ·
                  refine ⟨21254805517114020622701077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14169870344742680415134051 21254805517114020622701077)
                  ·
                    refine ⟨996319008614719716689113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21254805517114020622701077 996319008614719716689113)
                    ·
                      rfl

theorem cell23_5820973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5820973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5820973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5820973 prefixEnd_5820973 := by exact prefixLift 5820973
  have htrace : WordTrace (prefixWord ++ tailWord_5820973) baseStart_5820973 baseEnd_5820973 := by
    simpa [prefixWord, tailWord_5820973, baseEnd_5820973] using wordTrace_append hprefix tailTrace_5820973
  have hstable : (prefixWord ++ tailWord_5820973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5820973).length < 2 ^ (prefixWord ++ tailWord_5820973).sum := by decide
  have hdescent : baseEnd_5820973 < baseStart_5820973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5820973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821076 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 5]
def baseStart_5821076 : Nat := 118140960795 + 5821076 * 2 ^ 59
def prefixEnd_5821076 : Nat := 4983230072969 + 3 ^ 40 * 5821076 * 2
def baseEnd_5821076 : Nat := 332112212705730249675485

theorem tailTrace_5821076 : CollatzResearch.WordTrace tailWord_5821076 prefixEnd_5821076 332112212705730249675485 := by
  unfold tailWord_5821076
  simp only [CollatzResearch.WordTrace]
  refine ⟨106156041929621643738369541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141541389239495524984492721 106156041929621643738369541)
  ·
    refine ⟨19904257861804058200944289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106156041929621643738369541 19904257861804058200944289)
    ·
      refine ⟨14928193396353043650708217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19904257861804058200944289 14928193396353043650708217)
      ·
        refine ⟨11196145047264782738031163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14928193396353043650708217 11196145047264782738031163)
        ·
          refine ⟨16794217570897174107046745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11196145047264782738031163 16794217570897174107046745)
          ·
            refine ⟨12595663178172880580285059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16794217570897174107046745 12595663178172880580285059)
            ·
              refine ⟨18893494767259320870427589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12595663178172880580285059 18893494767259320870427589)
              ·
                refine ⟨3542530268861122663205173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18893494767259320870427589 3542530268861122663205173)
                ·
                  refine ⟨332112212705730249675485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542530268861122663205173 332112212705730249675485)
                  ·
                    rfl

theorem cell23_5821076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_5821076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821076 prefixEnd_5821076 := by exact prefixLift 5821076
  have htrace : WordTrace (prefixWord ++ tailWord_5821076) baseStart_5821076 baseEnd_5821076 := by
    simpa [prefixWord, tailWord_5821076, baseEnd_5821076] using wordTrace_append hprefix tailTrace_5821076
  have hstable : (prefixWord ++ tailWord_5821076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821076).length < 2 ^ (prefixWord ++ tailWord_5821076).sum := by decide
  have hdescent : baseEnd_5821076 < baseStart_5821076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821092 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_5821092 : Nat := 118140960795 + 5821092 * 2 ^ 59
def prefixEnd_5821092 : Nat := 4983230072969 + 3 ^ 40 * 5821092 * 2
def baseEnd_5821092 : Nat := 2989018130042044184479291

theorem tailTrace_5821092 : CollatzResearch.WordTrace tailWord_5821092 prefixEnd_5821092 2989018130042044184479291 := by
  unfold tailWord_5821092
  simp only [CollatzResearch.WordTrace]
  refine ⟨106156333713592661104660765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141541778284790214806214353 106156333713592661104660765)
  ·
    refine ⟨39808625142597247914247787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106156333713592661104660765 39808625142597247914247787)
    ·
      refine ⟨59712937713895871871371681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39808625142597247914247787 59712937713895871871371681)
      ·
        refine ⟨44784703285421903903528761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59712937713895871871371681 44784703285421903903528761)
        ·
          refine ⟨33588527464066427927646571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44784703285421903903528761 33588527464066427927646571)
          ·
            refine ⟨50382791196099641891469857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33588527464066427927646571 50382791196099641891469857)
            ·
              refine ⟨37787093397074731418602393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50382791196099641891469857 37787093397074731418602393)
              ·
                refine ⟨28340320047806048563951795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37787093397074731418602393 28340320047806048563951795)
                ·
                  refine ⟨42510480071709072845927693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28340320047806048563951795 42510480071709072845927693)
                  ·
                    refine ⟨15941430026890902317222885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42510480071709072845927693 15941430026890902317222885)
                    ·
                      refine ⟨2989018130042044184479291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15941430026890902317222885 2989018130042044184479291)
                      ·
                        rfl

theorem cell23_5821092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_5821092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821092 prefixEnd_5821092 := by exact prefixLift 5821092
  have htrace : WordTrace (prefixWord ++ tailWord_5821092) baseStart_5821092 baseEnd_5821092 := by
    simpa [prefixWord, tailWord_5821092, baseEnd_5821092] using wordTrace_append hprefix tailTrace_5821092
  have hstable : (prefixWord ++ tailWord_5821092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821092).length < 2 ^ (prefixWord ++ tailWord_5821092).sum := by decide
  have hdescent : baseEnd_5821092 < baseStart_5821092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821109 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5821109 : Nat := 118140960795 + 5821109 * 2 ^ 59
def prefixEnd_5821109 : Nat := 4983230072969 + 3 ^ 40 * 5821109 * 2
def baseEnd_5821109 : Nat := 2989026859213170617966713

theorem tailTrace_5821109 : CollatzResearch.WordTrace tailWord_5821109 prefixEnd_5821109 2989026859213170617966713 := by
  unfold tailWord_5821109
  simp only [CollatzResearch.WordTrace]
  refine ⟨212313287468123734112690381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141542191645415822741793587 212313287468123734112690381)
  ·
    refine ⟨79617482800546400292258893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212313287468123734112690381 79617482800546400292258893)
    ·
      refine ⟨29856556050204900109597085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79617482800546400292258893 29856556050204900109597085)
      ·
        refine ⟨11196208518826837541098907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29856556050204900109597085 11196208518826837541098907)
        ·
          refine ⟨16794312778240256311648361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11196208518826837541098907 16794312778240256311648361)
          ·
            refine ⟨12595734583680192233736271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16794312778240256311648361 12595734583680192233736271)
            ·
              refine ⟨18893601875520288350604407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12595734583680192233736271 18893601875520288350604407)
              ·
                refine ⟨28340402813280432525906611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18893601875520288350604407 28340402813280432525906611)
                ·
                  refine ⟨42510604219920648788859917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28340402813280432525906611 42510604219920648788859917)
                  ·
                    refine ⟨15941476582470243295822469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42510604219920648788859917 15941476582470243295822469)
                    ·
                      refine ⟨2989026859213170617966713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15941476582470243295822469 2989026859213170617966713)
                      ·
                        rfl

theorem cell23_5821109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5821109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821109 prefixEnd_5821109 := by exact prefixLift 5821109
  have htrace : WordTrace (prefixWord ++ tailWord_5821109) baseStart_5821109 baseEnd_5821109 := by
    simpa [prefixWord, tailWord_5821109, baseEnd_5821109] using wordTrace_append hprefix tailTrace_5821109
  have hstable : (prefixWord ++ tailWord_5821109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821109).length < 2 ^ (prefixWord ++ tailWord_5821109).sum := by decide
  have hdescent : baseEnd_5821109 < baseStart_5821109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821169 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_5821169 : Nat := 118140960795 + 5821169 * 2 ^ 59
def prefixEnd_5821169 : Nat := 4983230072969 + 3 ^ 40 * 5821169 * 2
def baseEnd_5821169 : Nat := 2989057668052440383216437

theorem tailTrace_5821169 : CollatzResearch.WordTrace tailWord_5821169 prefixEnd_5821169 2989057668052440383216437 := by
  unfold tailWord_5821169
  simp only [CollatzResearch.WordTrace]
  refine ⟨212315475847906364359874561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141543650565270909573249707 212315475847906364359874561)
  ·
    refine ⟨159236606885929773269905921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212315475847906364359874561 159236606885929773269905921)
    ·
      refine ⟨119427455164447329952429441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159236606885929773269905921 119427455164447329952429441)
      ·
        refine ⟨89570591373335497464322081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119427455164447329952429441 89570591373335497464322081)
        ·
          refine ⟨67177943530001623098241561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89570591373335497464322081 67177943530001623098241561)
          ·
            refine ⟨50383457647501217323681171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67177943530001623098241561 50383457647501217323681171)
            ·
              refine ⟨75575186471251825985521757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50383457647501217323681171 75575186471251825985521757)
              ·
                refine ⟨28340694926719434744570659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75575186471251825985521757 28340694926719434744570659)
                ·
                  refine ⟨42511042390079152116855989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28340694926719434744570659 42511042390079152116855989)
                  ·
                    refine ⟨3985410224069920510955249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42511042390079152116855989 3985410224069920510955249)
                    ·
                      refine ⟨2989057668052440383216437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985410224069920510955249 2989057668052440383216437)
                      ·
                        rfl

theorem cell23_5821169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_5821169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821169 prefixEnd_5821169 := by exact prefixLift 5821169
  have htrace : WordTrace (prefixWord ++ tailWord_5821169) baseStart_5821169 baseEnd_5821169 := by
    simpa [prefixWord, tailWord_5821169, baseEnd_5821169] using wordTrace_append hprefix tailTrace_5821169
  have hstable : (prefixWord ++ tailWord_5821169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821169).length < 2 ^ (prefixWord ++ tailWord_5821169).sum := by decide
  have hdescent : baseEnd_5821169 < baseStart_5821169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821216 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5821216 : Nat := 118140960795 + 5821216 * 2 ^ 59
def prefixEnd_5821216 : Nat := 4983230072969 + 3 ^ 40 * 5821216 * 2
def baseEnd_5821216 : Nat := 2989081801643201699328721

theorem tailTrace_5821216 : CollatzResearch.WordTrace tailWord_5821216 prefixEnd_5821216 2989081801643201699328721 := by
  unfold tailWord_5821216
  simp only [CollatzResearch.WordTrace]
  refine ⟨106158595039368045693417751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141544793385824060924557001 106158595039368045693417751)
  ·
    refine ⟨159237892559052068540126627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106158595039368045693417751 159237892559052068540126627)
    ·
      refine ⟨238856838838578102810189941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159237892559052068540126627 238856838838578102810189941)
      ·
        refine ⟨22392828641116697138455307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238856838838578102810189941 22392828641116697138455307)
        ·
          refine ⟨33589242961675045707682961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22392828641116697138455307 33589242961675045707682961)
          ·
            refine ⟨25191932221256284280762221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33589242961675045707682961 25191932221256284280762221)
            ·
              refine ⟨9446974582971106605285833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25191932221256284280762221 9446974582971106605285833)
              ·
                refine ⟨7085230937228329953964375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9446974582971106605285833 7085230937228329953964375)
                ·
                  refine ⟨10627846405842494930946563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085230937228329953964375 10627846405842494930946563)
                  ·
                    refine ⟨15941769608763742396419845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10627846405842494930946563 15941769608763742396419845)
                    ·
                      refine ⟨2989081801643201699328721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15941769608763742396419845 2989081801643201699328721)
                      ·
                        rfl

theorem cell23_5821216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5821216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821216 prefixEnd_5821216 := by exact prefixLift 5821216
  have htrace : WordTrace (prefixWord ++ tailWord_5821216) baseStart_5821216 baseEnd_5821216 := by
    simpa [prefixWord, tailWord_5821216, baseEnd_5821216] using wordTrace_append hprefix tailTrace_5821216
  have hstable : (prefixWord ++ tailWord_5821216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821216).length < 2 ^ (prefixWord ++ tailWord_5821216).sum := by decide
  have hdescent : baseEnd_5821216 < baseStart_5821216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821266 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_5821266 : Nat := 118140960795 + 5821266 * 2 ^ 59
def prefixEnd_5821266 : Nat := 4983230072969 + 3 ^ 40 * 5821266 * 2
def baseEnd_5821266 : Nat := 2989107475675926503703491

theorem tailTrace_5821266 : CollatzResearch.WordTrace tailWord_5821266 prefixEnd_5821266 2989107475675926503703491 := by
  unfold tailWord_5821266
  simp only [CollatzResearch.WordTrace]
  refine ⟨53079753432138737481538913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141546009152369966617437101 53079753432138737481538913)
  ·
    refine ⟨39809815074104053111154185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53079753432138737481538913 39809815074104053111154185)
    ·
      refine ⟨29857361305578039833365639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39809815074104053111154185 29857361305578039833365639)
      ·
        refine ⟨44786041958367059750048459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29857361305578039833365639 44786041958367059750048459)
        ·
          refine ⟨67179062937550589625072689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44786041958367059750048459 67179062937550589625072689)
          ·
            refine ⟨50384297203162942218804517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67179062937550589625072689 50384297203162942218804517)
            ·
              refine ⟨9447055725593051666025847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50384297203162942218804517 9447055725593051666025847)
              ·
                refine ⟨14170583588389577499038771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9447055725593051666025847 14170583588389577499038771)
                ·
                  refine ⟨21255875382584366248558157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14170583588389577499038771 21255875382584366248558157)
                  ·
                    refine ⟨7970953268469137343209309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21255875382584366248558157 7970953268469137343209309)
                    ·
                      refine ⟨2989107475675926503703491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7970953268469137343209309 2989107475675926503703491)
                      ·
                        rfl

theorem cell23_5821266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_5821266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821266 prefixEnd_5821266 := by exact prefixLift 5821266
  have htrace : WordTrace (prefixWord ++ tailWord_5821266) baseStart_5821266 baseEnd_5821266 := by
    simpa [prefixWord, tailWord_5821266, baseEnd_5821266] using wordTrace_append hprefix tailTrace_5821266
  have hstable : (prefixWord ++ tailWord_5821266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821266).length < 2 ^ (prefixWord ++ tailWord_5821266).sum := by decide
  have hdescent : baseEnd_5821266 < baseStart_5821266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821309 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_5821309 : Nat := 118140960795 + 5821309 * 2 ^ 59
def prefixEnd_5821309 : Nat := 4983230072969 + 3 ^ 40 * 5821309 * 2
def baseEnd_5821309 : Nat := 2989129555344069835465793

theorem tailTrace_5821309 : CollatzResearch.WordTrace tailWord_5821309 prefixEnd_5821309 2989129555344069835465793 := by
  unfold tailWord_5821309
  simp only [CollatzResearch.WordTrace]
  refine ⟨212320582067399168269970981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141547054711599445513313987 212320582067399168269970981)
  ·
    refine ⟨39810109137637344050619559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212320582067399168269970981 39810109137637344050619559)
    ·
      refine ⟨59715163706456016075929339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39810109137637344050619559 59715163706456016075929339)
      ·
        refine ⟨89572745559684024113894009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59715163706456016075929339 89572745559684024113894009)
        ·
          refine ⟨67179559169763018085420507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89572745559684024113894009 67179559169763018085420507)
          ·
            refine ⟨100769338754644527128130761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67179559169763018085420507 100769338754644527128130761)
            ·
              refine ⟨75577004065983395346098071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100769338754644527128130761 75577004065983395346098071)
              ·
                refine ⟨113365506098975093019147107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75577004065983395346098071 113365506098975093019147107)
                ·
                  refine ⟨170048259148462639528720661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113365506098975093019147107 170048259148462639528720661)
                  ·
                    refine ⟨7971012147584186227908781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170048259148462639528720661 7971012147584186227908781)
                    ·
                      refine ⟨2989129555344069835465793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971012147584186227908781 2989129555344069835465793)
                      ·
                        rfl

theorem cell23_5821309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_5821309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821309 prefixEnd_5821309 := by exact prefixLift 5821309
  have htrace : WordTrace (prefixWord ++ tailWord_5821309) baseStart_5821309 baseEnd_5821309 := by
    simpa [prefixWord, tailWord_5821309, baseEnd_5821309] using wordTrace_append hprefix tailTrace_5821309
  have hstable : (prefixWord ++ tailWord_5821309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821309).length < 2 ^ (prefixWord ++ tailWord_5821309).sum := by decide
  have hdescent : baseEnd_5821309 < baseStart_5821309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821323 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 2, 2, 2]
def baseStart_5821323 : Nat := 118140960795 + 5821323 * 2 ^ 59
def prefixEnd_5821323 : Nat := 4983230072969 + 3 ^ 40 * 5821323 * 2
def baseEnd_5821323 : Nat := 2989136744073232780690729

theorem tailTrace_5821323 : CollatzResearch.WordTrace tailWord_5821323 prefixEnd_5821323 2989136744073232780690729 := by
  unfold tailWord_5821323
  simp only [CollatzResearch.WordTrace]
  refine ⟨212321092689348448660980623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141547395126232299107320415 212321092689348448660980623)
  ·
    refine ⟨318481639034022672991470935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212321092689348448660980623 318481639034022672991470935)
    ·
      refine ⟨477722458551034009487206403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318481639034022672991470935 477722458551034009487206403)
      ·
        refine ⟨716583687826551014230809605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477722458551034009487206403 716583687826551014230809605)
        ·
          refine ⟨134359441467478315168276801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 716583687826551014230809605 134359441467478315168276801)
          ·
            refine ⟨100769581100608736376207601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134359441467478315168276801 100769581100608736376207601)
            ·
              refine ⟨75577185825456552282155701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100769581100608736376207601 75577185825456552282155701)
              ·
                refine ⟨7085361171136551776452097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75577185825456552282155701 7085361171136551776452097)
                ·
                  refine ⟨5314020878352413832339073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085361171136551776452097 5314020878352413832339073)
                  ·
                    refine ⟨3985515658764310374254305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314020878352413832339073 3985515658764310374254305)
                    ·
                      refine ⟨2989136744073232780690729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985515658764310374254305 2989136744073232780690729)
                      ·
                        rfl

theorem cell23_5821323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 2, 2].length) (baseStart_5821323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821323 prefixEnd_5821323 := by exact prefixLift 5821323
  have htrace : WordTrace (prefixWord ++ tailWord_5821323) baseStart_5821323 baseEnd_5821323 := by
    simpa [prefixWord, tailWord_5821323, baseEnd_5821323] using wordTrace_append hprefix tailTrace_5821323
  have hstable : (prefixWord ++ tailWord_5821323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821323).length < 2 ^ (prefixWord ++ tailWord_5821323).sum := by decide
  have hdescent : baseEnd_5821323 < baseStart_5821323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821369 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5821369 : Nat := 118140960795 + 5821369 * 2 ^ 59
def prefixEnd_5821369 : Nat := 4983230072969 + 3 ^ 40 * 5821369 * 2
def baseEnd_5821369 : Nat := 2989160364183339600715517

theorem tailTrace_5821369 : CollatzResearch.WordTrace tailWord_5821369 prefixEnd_5821369 2989160364183339600715517 := by
  unfold tailWord_5821369
  simp only [CollatzResearch.WordTrace]
  refine ⟨212322770447181798517155161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141548513631454532344770107 212322770447181798517155161)
  ·
    refine ⟨159242077835386348887866371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212322770447181798517155161 159242077835386348887866371)
    ·
      refine ⟨238863116753079523331799557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159242077835386348887866371 238863116753079523331799557)
      ·
        refine ⟨44786834391202410624712417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238863116753079523331799557 44786834391202410624712417)
        ·
          refine ⟨33590125793401807968534313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44786834391202410624712417 33590125793401807968534313)
          ·
            refine ⟨25192594345051355976400735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33590125793401807968534313 25192594345051355976400735)
            ·
              refine ⟨37788891517577033964601103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25192594345051355976400735 37788891517577033964601103)
              ·
                refine ⟨56683337276365550946901655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37788891517577033964601103 56683337276365550946901655)
                ·
                  refine ⟨85025005914548326420352483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56683337276365550946901655 85025005914548326420352483)
                  ·
                    refine ⟨127537508871822489630528725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85025005914548326420352483 127537508871822489630528725)
                    ·
                      refine ⟨2989160364183339600715517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127537508871822489630528725 2989160364183339600715517)
                      ·
                        rfl

theorem cell23_5821369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5821369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821369 prefixEnd_5821369 := by exact prefixLift 5821369
  have htrace : WordTrace (prefixWord ++ tailWord_5821369) baseStart_5821369 baseEnd_5821369 := by
    simpa [prefixWord, tailWord_5821369, baseEnd_5821369] using wordTrace_append hprefix tailTrace_5821369
  have hstable : (prefixWord ++ tailWord_5821369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821369).length < 2 ^ (prefixWord ++ tailWord_5821369).sum := by decide
  have hdescent : baseEnd_5821369 < baseStart_5821369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821409 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5821409 : Nat := 118140960795 + 5821409 * 2 ^ 59
def prefixEnd_5821409 : Nat := 4983230072969 + 3 ^ 40 * 5821409 * 2
def baseEnd_5821409 : Nat := 2989180903409519444215333

theorem tailTrace_5821409 : CollatzResearch.WordTrace tailWord_5821409 prefixEnd_5821409 2989180903409519444215333 := by
  unfold tailWord_5821409
  simp only [CollatzResearch.WordTrace]
  refine ⟨212324229367036885348611281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141549486244691256899074187 212324229367036885348611281)
  ·
    refine ⟨159243172025277664011458461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212324229367036885348611281 159243172025277664011458461)
    ·
      refine ⟨59716189509479124004296923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159243172025277664011458461 59716189509479124004296923)
      ·
        refine ⟨89574284264218686006445385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59716189509479124004296923 89574284264218686006445385)
        ·
          refine ⟨67180713198164014504834039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89574284264218686006445385 67180713198164014504834039)
          ·
            refine ⟨100771069797246021757251059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67180713198164014504834039 100771069797246021757251059)
            ·
              refine ⟨151156604695869032635876589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100771069797246021757251059 151156604695869032635876589)
              ·
                refine ⟨56683726760950887238453721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151156604695869032635876589 56683726760950887238453721)
                ·
                  refine ⟨42512795070713165428840291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56683726760950887238453721 42512795070713165428840291)
                  ·
                    refine ⟨63769192606069748143260437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42512795070713165428840291 63769192606069748143260437)
                    ·
                      refine ⟨2989180903409519444215333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63769192606069748143260437 2989180903409519444215333)
                      ·
                        rfl

theorem cell23_5821409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5821409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821409 prefixEnd_5821409 := by exact prefixLift 5821409
  have htrace : WordTrace (prefixWord ++ tailWord_5821409) baseStart_5821409 baseEnd_5821409 := by
    simpa [prefixWord, tailWord_5821409, baseEnd_5821409] using wordTrace_append hprefix tailTrace_5821409
  have hstable : (prefixWord ++ tailWord_5821409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821409).length < 2 ^ (prefixWord ++ tailWord_5821409).sum := by decide
  have hdescent : baseEnd_5821409 < baseStart_5821409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821430 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5821430 : Nat := 118140960795 + 5821430 * 2 ^ 59
def prefixEnd_5821430 : Nat := 4983230072969 + 3 ^ 40 * 5821430 * 2
def baseEnd_5821430 : Nat := 2989191686503263862052737

theorem tailTrace_5821430 : CollatzResearch.WordTrace tailWord_5821430 prefixEnd_5821430 2989191686503263862052737 := by
  unfold tailWord_5821430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13270312206247550370945359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141549996866640537290083829 13270312206247550370945359)
  ·
    refine ⟨19905468309371325556418039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13270312206247550370945359 19905468309371325556418039)
    ·
      refine ⟨29858202464056988334627059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19905468309371325556418039 29858202464056988334627059)
      ·
        refine ⟨44787303696085482501940589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29858202464056988334627059 44787303696085482501940589)
        ·
          refine ⟨16795238886032055938227721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44787303696085482501940589 16795238886032055938227721)
          ·
            refine ⟨12596429164524041953670791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16795238886032055938227721 12596429164524041953670791)
            ·
              refine ⟨18894643746786062930506187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12596429164524041953670791 18894643746786062930506187)
              ·
                refine ⟨28341965620179094395759281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18894643746786062930506187 28341965620179094395759281)
                ·
                  refine ⟨21256474215134320796819461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28341965620179094395759281 21256474215134320796819461)
                  ·
                    refine ⟨3985588915337685149403649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21256474215134320796819461 3985588915337685149403649)
                    ·
                      refine ⟨2989191686503263862052737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985588915337685149403649 2989191686503263862052737)
                      ·
                        rfl

theorem cell23_5821430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5821430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821430 prefixEnd_5821430 := by exact prefixLift 5821430
  have htrace : WordTrace (prefixWord ++ tailWord_5821430) baseStart_5821430 baseEnd_5821430 := by
    simpa [prefixWord, tailWord_5821430, baseEnd_5821430] using wordTrace_append hprefix tailTrace_5821430
  have hstable : (prefixWord ++ tailWord_5821430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821430).length < 2 ^ (prefixWord ++ tailWord_5821430).sum := by decide
  have hdescent : baseEnd_5821430 < baseStart_5821430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821436 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 6]
def baseStart_5821436 : Nat := 118140960795 + 5821436 * 2 ^ 59
def prefixEnd_5821436 : Nat := 4983230072969 + 3 ^ 40 * 5821436 * 2
def baseEnd_5821436 : Nat := 332132751931910093175301

theorem tailTrace_5821436 : CollatzResearch.WordTrace tailWord_5821436 prefixEnd_5821436 332132751931910093175301 := by
  unfold tailWord_5821436
  simp only [CollatzResearch.WordTrace]
  refine ⟨106162607068969534479922081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141550142758626045973229441 106162607068969534479922081)
  ·
    refine ⟨79621955301727150859941561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106162607068969534479922081 79621955301727150859941561)
    ·
      refine ⟨59716466476295363144956171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79621955301727150859941561 59716466476295363144956171)
      ·
        refine ⟨89574699714443044717434257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59716466476295363144956171 89574699714443044717434257)
        ·
          refine ⟨67181024785832283538075693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89574699714443044717434257 67181024785832283538075693)
          ·
            refine ⟨25192884294687106326778385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67181024785832283538075693 25192884294687106326778385)
            ·
              refine ⟨18894663221015329745083789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25192884294687106326778385 18894663221015329745083789)
              ·
                refine ⟨7085498707880748654406421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18894663221015329745083789 7085498707880748654406421)
                ·
                  refine ⟨332132751931910093175301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7085498707880748654406421 332132751931910093175301)
                  ·
                    rfl

theorem cell23_5821436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_5821436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821436 prefixEnd_5821436 := by exact prefixLift 5821436
  have htrace : WordTrace (prefixWord ++ tailWord_5821436) baseStart_5821436 baseEnd_5821436 := by
    simpa [prefixWord, tailWord_5821436, baseEnd_5821436] using wordTrace_append hprefix tailTrace_5821436
  have hstable : (prefixWord ++ tailWord_5821436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821436).length < 2 ^ (prefixWord ++ tailWord_5821436).sum := by decide
  have hdescent : baseEnd_5821436 < baseStart_5821436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821450 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_5821450 : Nat := 118140960795 + 5821450 * 2 ^ 59
def prefixEnd_5821450 : Nat := 4983230072969 + 3 ^ 40 * 5821450 * 2
def baseEnd_5821450 : Nat := 2989201956116353783802645

theorem tailTrace_5821450 : CollatzResearch.WordTrace tailWord_5821450 prefixEnd_5821450 2989201956116353783802645 := by
  unfold tailWord_5821450
  simp only [CollatzResearch.WordTrace]
  refine ⟨53081431189972087337713451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141550483173258899567235869 53081431189972087337713451)
  ·
    refine ⟨79622146784958131006570177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53081431189972087337713451 79622146784958131006570177)
    ·
      refine ⟨59716610088718598254927633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79622146784958131006570177 59716610088718598254927633)
      ·
        refine ⟨44787457566538948691195725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59716610088718598254927633 44787457566538948691195725)
        ·
          refine ⟨16795296587452105759198397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44787457566538948691195725 16795296587452105759198397)
          ·
            refine ⟨6298236220294539659699399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16795296587452105759198397 6298236220294539659699399)
            ·
              refine ⟨9447354330441809489549099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298236220294539659699399 9447354330441809489549099)
              ·
                refine ⟨14171031495662714234323649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9447354330441809489549099 14171031495662714234323649)
                ·
                  refine ⟨10628273621747035675742737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14171031495662714234323649 10628273621747035675742737)
                  ·
                    refine ⟨7971205216310276756807053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10628273621747035675742737 7971205216310276756807053)
                    ·
                      refine ⟨2989201956116353783802645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971205216310276756807053 2989201956116353783802645)
                      ·
                        rfl

theorem cell23_5821450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_5821450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821450 prefixEnd_5821450 := by exact prefixLift 5821450
  have htrace : WordTrace (prefixWord ++ tailWord_5821450) baseStart_5821450 baseEnd_5821450 := by
    simpa [prefixWord, tailWord_5821450, baseEnd_5821450] using wordTrace_append hprefix tailTrace_5821450
  have hstable : (prefixWord ++ tailWord_5821450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821450).length < 2 ^ (prefixWord ++ tailWord_5821450).sum := by decide
  have hdescent : baseEnd_5821450 < baseStart_5821450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821459 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_5821459 : Nat := 118140960795 + 5821459 * 2 ^ 59
def prefixEnd_5821459 : Nat := 4983230072969 + 3 ^ 40 * 5821459 * 2
def baseEnd_5821459 : Nat := 2989206577442244248590103

theorem tailTrace_5821459 : CollatzResearch.WordTrace tailWord_5821459 prefixEnd_5821459 2989206577442244248590103 := by
  unfold tailWord_5821459
  simp only [CollatzResearch.WordTrace]
  refine ⟨212326053016855743887931431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141550702011237162591954287 212326053016855743887931431)
  ·
    refine ⟨318489079525283615831897147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212326053016855743887931431 318489079525283615831897147)
    ·
      refine ⟨477733619287925423747845721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318489079525283615831897147 477733619287925423747845721)
      ·
        refine ⟨358300214465944067810884291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477733619287925423747845721 358300214465944067810884291)
        ·
          refine ⟨537450321698916101716326437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358300214465944067810884291 537450321698916101716326437)
          ·
            refine ⟨100771935318546769071811207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 537450321698916101716326437 100771935318546769071811207)
            ·
              refine ⟨151157902977820153607716811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100771935318546769071811207 151157902977820153607716811)
              ·
                refine ⟨226736854466730230411575217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151157902977820153607716811 226736854466730230411575217)
                ·
                  refine ⟨170052640850047672808681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226736854466730230411575217 170052640850047672808681413)
                  ·
                    refine ⟨31884870159383938651627765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170052640850047672808681413 31884870159383938651627765)
                    ·
                      refine ⟨2989206577442244248590103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31884870159383938651627765 2989206577442244248590103)
                      ·
                        rfl

theorem cell23_5821459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_5821459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821459 prefixEnd_5821459 := by exact prefixLift 5821459
  have htrace : WordTrace (prefixWord ++ tailWord_5821459) baseStart_5821459 baseEnd_5821459 := by
    simpa [prefixWord, tailWord_5821459, baseEnd_5821459] using wordTrace_append hprefix tailTrace_5821459
  have hstable : (prefixWord ++ tailWord_5821459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821459).length < 2 ^ (prefixWord ++ tailWord_5821459).sum := by decide
  have hdescent : baseEnd_5821459 < baseStart_5821459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821516 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5821516 : Nat := 118140960795 + 5821516 * 2 ^ 59
def prefixEnd_5821516 : Nat := 4983230072969 + 3 ^ 40 * 5821516 * 2
def baseEnd_5821516 : Nat := 2989235845839550525577341

theorem tailTrace_5821516 : CollatzResearch.WordTrace tailWord_5821516 prefixEnd_5821516 2989235845839550525577341 := by
  unfold tailWord_5821516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106164065988824621311378201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141552087985099495081837601 106164065988824621311378201)
  ·
    refine ⟨79623049491618465983533651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106164065988824621311378201 79623049491618465983533651)
    ·
      refine ⟨119434574237427698975300477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79623049491618465983533651 119434574237427698975300477)
      ·
        refine ⟨44787965339035387115737679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119434574237427698975300477 44787965339035387115737679)
        ·
          refine ⟨67181948008553080673606519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44787965339035387115737679 67181948008553080673606519)
          ·
            refine ⟨100772922012829621010409779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67181948008553080673606519 100772922012829621010409779)
            ·
              refine ⟨151159383019244431515614669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100772922012829621010409779 151159383019244431515614669)
              ·
                refine ⟨56684768632216661818355501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151159383019244431515614669 56684768632216661818355501)
                ·
                  refine ⟨21256788237081248181883313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56684768632216661818355501 21256788237081248181883313)
                  ·
                    refine ⟨15942591177810936136412485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21256788237081248181883313 15942591177810936136412485)
                    ·
                      refine ⟨2989235845839550525577341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15942591177810936136412485 2989235845839550525577341)
                      ·
                        rfl

theorem cell23_5821516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5821516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821516 prefixEnd_5821516 := by exact prefixLift 5821516
  have htrace : WordTrace (prefixWord ++ tailWord_5821516) baseStart_5821516 baseEnd_5821516 := by
    simpa [prefixWord, tailWord_5821516, baseEnd_5821516] using wordTrace_append hprefix tailTrace_5821516
  have hstable : (prefixWord ++ tailWord_5821516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821516).length < 2 ^ (prefixWord ++ tailWord_5821516).sum := by decide
  have hdescent : baseEnd_5821516 < baseStart_5821516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821537 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_5821537 : Nat := 118140960795 + 5821537 * 2 ^ 59
def prefixEnd_5821537 : Nat := 4983230072969 + 3 ^ 40 * 5821537 * 2
def baseEnd_5821537 : Nat := 2989246628933294943414745

theorem tailTrace_5821537 : CollatzResearch.WordTrace tailWord_5821537 prefixEnd_5821537 2989246628933294943414745 := by
  unfold tailWord_5821537
  simp only [CollatzResearch.WordTrace]
  refine ⟨212328897910573163209270865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141552598607048775472847243 212328897910573163209270865)
  ·
    refine ⟨159246673432929872406953149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212328897910573163209270865 159246673432929872406953149)
    ·
      refine ⟨59717502537348702152607431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159246673432929872406953149 59717502537348702152607431)
      ·
        refine ⟨89576253806023053228911147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59717502537348702152607431 89576253806023053228911147)
        ·
          refine ⟨134364380709034579843366721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89576253806023053228911147 134364380709034579843366721)
          ·
            refine ⟨100773285531775934882525041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134364380709034579843366721 100773285531775934882525041)
            ·
              refine ⟨75579964148831951161893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100773285531775934882525041 75579964148831951161893781)
              ·
                refine ⟨3542810819476497710713771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75579964148831951161893781 3542810819476497710713771)
                ·
                  refine ⟨5314216229214746566070657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542810819476497710713771 5314216229214746566070657)
                  ·
                    refine ⟨3985662171911059924552993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314216229214746566070657 3985662171911059924552993)
                    ·
                      refine ⟨2989246628933294943414745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985662171911059924552993 2989246628933294943414745)
                      ·
                        rfl

theorem cell23_5821537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_5821537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821537 prefixEnd_5821537 := by exact prefixLift 5821537
  have htrace : WordTrace (prefixWord ++ tailWord_5821537) baseStart_5821537 baseEnd_5821537 := by
    simpa [prefixWord, tailWord_5821537, baseEnd_5821537] using wordTrace_append hprefix tailTrace_5821537
  have hstable : (prefixWord ++ tailWord_5821537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821537).length < 2 ^ (prefixWord ++ tailWord_5821537).sum := by decide
  have hdescent : baseEnd_5821537 < baseStart_5821537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821553 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_5821553 : Nat := 118140960795 + 5821553 * 2 ^ 59
def prefixEnd_5821553 : Nat := 4983230072969 + 3 ^ 40 * 5821553 * 2
def baseEnd_5821553 : Nat := 2989254844623766880814671

theorem tailTrace_5821553 : CollatzResearch.WordTrace tailWord_5821553 prefixEnd_5821553 2989254844623766880814671 := by
  unfold tailWord_5821553
  simp only [CollatzResearch.WordTrace]
  refine ⟨212329481478515197941853313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141552987652343465294568875 212329481478515197941853313)
  ·
    refine ⟨159247111108886398456389985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212329481478515197941853313 159247111108886398456389985)
    ·
      refine ⟨119435333331664798842292489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159247111108886398456389985 119435333331664798842292489)
      ·
        refine ⟨89576499998748599131719367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119435333331664798842292489 89576499998748599131719367)
        ·
          refine ⟨134364749998122898697579051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89576499998748599131719367 134364749998122898697579051)
          ·
            refine ⟨201547124997184348046368577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134364749998122898697579051 201547124997184348046368577)
            ·
              refine ⟨151160343747888261034776433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201547124997184348046368577 151160343747888261034776433)
              ·
                refine ⟨113370257810916195776082325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151160343747888261034776433 113370257810916195776082325)
                ·
                  refine ⟨5314230834886696677003859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113370257810916195776082325 5314230834886696677003859)
                  ·
                    refine ⟨7971346252330045015505789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5314230834886696677003859 7971346252330045015505789)
                    ·
                      refine ⟨2989254844623766880814671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971346252330045015505789 2989254844623766880814671)
                      ·
                        rfl

theorem cell23_5821553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_5821553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821553 prefixEnd_5821553 := by exact prefixLift 5821553
  have htrace : WordTrace (prefixWord ++ tailWord_5821553) baseStart_5821553 baseEnd_5821553 := by
    simpa [prefixWord, tailWord_5821553, baseEnd_5821553] using wordTrace_append hprefix tailTrace_5821553
  have hstable : (prefixWord ++ tailWord_5821553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821553).length < 2 ^ (prefixWord ++ tailWord_5821553).sum := by decide
  have hdescent : baseEnd_5821553 < baseStart_5821553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821557 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5821557 : Nat := 118140960795 + 5821557 * 2 ^ 59
def prefixEnd_5821557 : Nat := 4983230072969 + 3 ^ 40 * 5821557 * 2
def baseEnd_5821557 : Nat := 2989256898546384865164653

theorem tailTrace_5821557 : CollatzResearch.WordTrace tailWord_5821557 prefixEnd_5821557 2989256898546384865164653 := by
  unfold tailWord_5821557
  simp only [CollatzResearch.WordTrace]
  refine ⟨212329627370500706624998925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141553084913667137749999283 212329627370500706624998925)
  ·
    refine ⟨79623610263937764984374597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212329627370500706624998925 79623610263937764984374597)
    ·
      refine ⟨14929426924488330934570237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79623610263937764984374597 14929426924488330934570237)
      ·
        refine ⟨5598535096683124100463839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14929426924488330934570237 5598535096683124100463839)
        ·
          refine ⟨8397802645024686150695759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598535096683124100463839 8397802645024686150695759)
          ·
            refine ⟨12596703967537029226043639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8397802645024686150695759 12596703967537029226043639)
            ·
              refine ⟨18895055951305543839065459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12596703967537029226043639 18895055951305543839065459)
              ·
                refine ⟨28342583926958315758598189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18895055951305543839065459 28342583926958315758598189)
                ·
                  refine ⟨10628468972609368409474321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28342583926958315758598189 10628468972609368409474321)
                  ·
                    refine ⟨7971351729457026307105741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10628468972609368409474321 7971351729457026307105741)
                    ·
                      refine ⟨2989256898546384865164653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971351729457026307105741 2989256898546384865164653)
                      ·
                        rfl

theorem cell23_5821557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5821557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821557 prefixEnd_5821557 := by exact prefixLift 5821557
  have htrace : WordTrace (prefixWord ++ tailWord_5821557) baseStart_5821557 baseEnd_5821557 := by
    simpa [prefixWord, tailWord_5821557, baseEnd_5821557] using wordTrace_append hprefix tailTrace_5821557
  have hstable : (prefixWord ++ tailWord_5821557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821557).length < 2 ^ (prefixWord ++ tailWord_5821557).sum := by decide
  have hdescent : baseEnd_5821557 < baseStart_5821557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821580 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_5821580 : Nat := 118140960795 + 5821580 * 2 ^ 59
def prefixEnd_5821580 : Nat := 4983230072969 + 3 ^ 40 * 5821580 * 2
def baseEnd_5821580 : Nat := 2989268708601438275177047

theorem tailTrace_5821580 : CollatzResearch.WordTrace tailWord_5821580 prefixEnd_5821580 2989268708601438275177047 := by
  unfold tailWord_5821580
  simp only [CollatzResearch.WordTrace]
  refine ⟨106165233124708690776543097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141553644166278254368724129 106165233124708690776543097)
  ·
    refine ⟨79623924843531518082407323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106165233124708690776543097 79623924843531518082407323)
    ·
      refine ⟨119435887265297277123610985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79623924843531518082407323 119435887265297277123610985)
      ·
        refine ⟨89576915448972957842708239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119435887265297277123610985 89576915448972957842708239)
        ·
          refine ⟨134365373173459436764062359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89576915448972957842708239 134365373173459436764062359)
          ·
            refine ⟨201548059760189155146093539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134365373173459436764062359 201548059760189155146093539)
            ·
              refine ⟨302322089640283732719140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201548059760189155146093539 302322089640283732719140309)
              ·
                refine ⟨7085673975944149985604851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 302322089640283732719140309 7085673975944149985604851)
                ·
                  refine ⟨10628510963916224978407277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085673975944149985604851 10628510963916224978407277)
                  ·
                    refine ⟨3985691611468584366902729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10628510963916224978407277 3985691611468584366902729)
                    ·
                      refine ⟨2989268708601438275177047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985691611468584366902729 2989268708601438275177047)
                      ·
                        rfl

theorem cell23_5821580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_5821580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821580 prefixEnd_5821580 := by exact prefixLift 5821580
  have htrace : WordTrace (prefixWord ++ tailWord_5821580) baseStart_5821580 baseEnd_5821580 := by
    simpa [prefixWord, tailWord_5821580, baseEnd_5821580] using wordTrace_append hprefix tailTrace_5821580
  have hstable : (prefixWord ++ tailWord_5821580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821580).length < 2 ^ (prefixWord ++ tailWord_5821580).sum := by decide
  have hdescent : baseEnd_5821580 < baseStart_5821580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821616 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 7]
def baseStart_5821616 : Nat := 118140960795 + 5821616 * 2 ^ 59
def prefixEnd_5821616 : Nat := 4983230072969 + 3 ^ 40 * 5821616 * 2
def baseEnd_5821616 : Nat := 332143021545000014925209

theorem tailTrace_5821616 : CollatzResearch.WordTrace tailWord_5821616 prefixEnd_5821616 332143021545000014925209 := by
  unfold tailWord_5821616
  simp only [CollatzResearch.WordTrace]
  refine ⟨106165889638643479850698351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141554519518191306467597801 106165889638643479850698351)
  ·
    refine ⟨159248834457965219776047527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106165889638643479850698351 159248834457965219776047527)
    ·
      refine ⟨238873251686947829664071291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159248834457965219776047527 238873251686947829664071291)
      ·
        refine ⟨358309877530421744496106937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238873251686947829664071291 358309877530421744496106937)
        ·
          refine ⟨268732408147816308372080203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358309877530421744496106937 268732408147816308372080203)
          ·
            refine ⟨403098612221724462558120305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268732408147816308372080203 403098612221724462558120305)
            ·
              refine ⟨302323959166293346918590229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403098612221724462558120305 302323959166293346918590229)
              ·
                refine ⟨14171435585920000636808917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302323959166293346918590229 14171435585920000636808917)
                ·
                  refine ⟨332143021545000014925209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14171435585920000636808917 332143021545000014925209)
                  ·
                    rfl

theorem cell23_5821616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_5821616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821616 prefixEnd_5821616 := by exact prefixLift 5821616
  have htrace : WordTrace (prefixWord ++ tailWord_5821616) baseStart_5821616 baseEnd_5821616 := by
    simpa [prefixWord, tailWord_5821616, baseEnd_5821616] using wordTrace_append hprefix tailTrace_5821616
  have hstable : (prefixWord ++ tailWord_5821616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821616).length < 2 ^ (prefixWord ++ tailWord_5821616).sum := by decide
  have hdescent : baseEnd_5821616 < baseStart_5821616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821626 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_5821626 : Nat := 118140960795 + 5821626 * 2 ^ 59
def prefixEnd_5821626 : Nat := 4983230072969 + 3 ^ 40 * 5821626 * 2
def baseEnd_5821626 : Nat := 2989292328711545095201835

theorem tailTrace_5821626 : CollatzResearch.WordTrace tailWord_5821626 prefixEnd_5821626 2989292328711545095201835 := by
  unfold tailWord_5821626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53083036001812682852315183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141554762671500487606173821 53083036001812682852315183)
  ·
    refine ⟨79624554002719024278472775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53083036001812682852315183 79624554002719024278472775)
    ·
      refine ⟨119436831004078536417709163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79624554002719024278472775 119436831004078536417709163)
      ·
        refine ⟨179155246506117804626563745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119436831004078536417709163 179155246506117804626563745)
        ·
          refine ⟨134366434879588353469922809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179155246506117804626563745 134366434879588353469922809)
          ·
            refine ⟨100774826159691265102442107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134366434879588353469922809 100774826159691265102442107)
            ·
              refine ⟨151162239239536897653663161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100774826159691265102442107 151162239239536897653663161)
              ·
                refine ⟨113371679429652673240247371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151162239239536897653663161 113371679429652673240247371)
                ·
                  refine ⟨170057519144479009860371057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113371679429652673240247371 170057519144479009860371057)
                  ·
                    refine ⟨127543139358359257395278293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170057519144479009860371057 127543139358359257395278293)
                    ·
                      refine ⟨2989292328711545095201835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127543139358359257395278293 2989292328711545095201835)
                      ·
                        rfl

theorem cell23_5821626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_5821626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821626 prefixEnd_5821626 := by exact prefixLift 5821626
  have htrace : WordTrace (prefixWord ++ tailWord_5821626) baseStart_5821626 baseEnd_5821626 := by
    simpa [prefixWord, tailWord_5821626, baseEnd_5821626] using wordTrace_append hprefix tailTrace_5821626
  have hstable : (prefixWord ++ tailWord_5821626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821626).length < 2 ^ (prefixWord ++ tailWord_5821626).sum := by decide
  have hdescent : baseEnd_5821626 < baseStart_5821626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821650 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_5821650 : Nat := 118140960795 + 5821650 * 2 ^ 59
def prefixEnd_5821650 : Nat := 4983230072969 + 3 ^ 40 * 5821650 * 2
def baseEnd_5821650 : Nat := 332144961360805889033525

theorem tailTrace_5821650 : CollatzResearch.WordTrace tailWord_5821650 prefixEnd_5821650 332144961360805889033525 := by
  unfold tailWord_5821650
  simp only [CollatzResearch.WordTrace]
  refine ⟨53083254839790945877033601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141555346239442522338756269 53083254839790945877033601)
  ·
    refine ⟨39812441129843209407775201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53083254839790945877033601 39812441129843209407775201)
    ·
      refine ⟨29859330847382407055831401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39812441129843209407775201 29859330847382407055831401)
      ·
        refine ⟨22394498135536805291873551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29859330847382407055831401 22394498135536805291873551)
        ·
          refine ⟨33591747203305207937810327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22394498135536805291873551 33591747203305207937810327)
          ·
            refine ⟨50387620804957811906715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33591747203305207937810327 50387620804957811906715491)
            ·
              refine ⟨75581431207436717860073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50387620804957811906715491 75581431207436717860073237)
              ·
                refine ⟨3542879587848596149690933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75581431207436717860073237 3542879587848596149690933)
                ·
                  refine ⟨332144961360805889033525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542879587848596149690933 332144961360805889033525)
                  ·
                    rfl

theorem cell23_5821650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_5821650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821650 prefixEnd_5821650 := by exact prefixLift 5821650
  have htrace : WordTrace (prefixWord ++ tailWord_5821650) baseStart_5821650 baseEnd_5821650 := by
    simpa [prefixWord, tailWord_5821650, baseEnd_5821650] using wordTrace_append hprefix tailTrace_5821650
  have hstable : (prefixWord ++ tailWord_5821650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821650).length < 2 ^ (prefixWord ++ tailWord_5821650).sum := by decide
  have hdescent : baseEnd_5821650 < baseStart_5821650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821661 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5821661 : Nat := 118140960795 + 5821661 * 2 ^ 59
def prefixEnd_5821661 : Nat := 4983230072969 + 3 ^ 40 * 5821661 * 2
def baseEnd_5821661 : Nat := 2989310300534452458264175

theorem tailTrace_5821661 : CollatzResearch.WordTrace tailWord_5821661 prefixEnd_5821661 2989310300534452458264175 := by
  unfold tailWord_5821661
  simp only [CollatzResearch.WordTrace]
  refine ⟨212333420562123932386784837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141555613708082621591189891 212333420562123932386784837)
  ·
    refine ⟨39812516355398237322522157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212333420562123932386784837 39812516355398237322522157)
    ·
      refine ⟨14929693633274338995945809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39812516355398237322522157 14929693633274338995945809)
      ·
        refine ⟨11197270224955754246959357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14929693633274338995945809 11197270224955754246959357)
        ·
          refine ⟨4198976334358407842609759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11197270224955754246959357 4198976334358407842609759)
          ·
            refine ⟨6298464501537611763914639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198976334358407842609759 6298464501537611763914639)
            ·
              refine ⟨9447696752306417645871959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298464501537611763914639 9447696752306417645871959)
              ·
                refine ⟨14171545128459626468807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9447696752306417645871959 14171545128459626468807939)
                ·
                  refine ⟨21257317692689439703211909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14171545128459626468807939 21257317692689439703211909)
                  ·
                    refine ⟨3985747067379269944352233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21257317692689439703211909 3985747067379269944352233)
                    ·
                      refine ⟨2989310300534452458264175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985747067379269944352233 2989310300534452458264175)
                      ·
                        rfl

theorem cell23_5821661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5821661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821661 prefixEnd_5821661 := by exact prefixLift 5821661
  have htrace : WordTrace (prefixWord ++ tailWord_5821661) baseStart_5821661 baseEnd_5821661 := by
    simpa [prefixWord, tailWord_5821661, baseEnd_5821661] using wordTrace_append hprefix tailTrace_5821661
  have hstable : (prefixWord ++ tailWord_5821661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821661).length < 2 ^ (prefixWord ++ tailWord_5821661).sum := by decide
  have hdescent : baseEnd_5821661 < baseStart_5821661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821683 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_5821683 : Nat := 118140960795 + 5821683 * 2 ^ 59
def prefixEnd_5821683 : Nat := 4983230072969 + 3 ^ 40 * 5821683 * 2
def baseEnd_5821683 : Nat := 2989321597108851372189073

theorem tailTrace_5821683 : CollatzResearch.WordTrace tailWord_5821683 prefixEnd_5821683 2989321597108851372189073 := by
  unfold tailWord_5821683
  simp only [CollatzResearch.WordTrace]
  refine ⟨212334222968044230144085703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141556148645362820096057135 212334222968044230144085703)
  ·
    refine ⟨318501334452066345216128555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212334222968044230144085703 318501334452066345216128555)
    ·
      refine ⟨477752001678099517824192833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318501334452066345216128555 477752001678099517824192833)
      ·
        refine ⟨358314001258574638368144625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477752001678099517824192833 358314001258574638368144625)
        ·
          refine ⟨268735500943930978776108469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358314001258574638368144625 268735500943930978776108469)
          ·
            refine ⟨25193953213493529260260169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268735500943930978776108469 25193953213493529260260169)
            ·
              refine ⟨18895464910120146945195127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25193953213493529260260169 18895464910120146945195127)
              ·
                refine ⟨28343197365180220417792691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18895464910120146945195127 28343197365180220417792691)
                ·
                  refine ⟨42514796047770330626689037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28343197365180220417792691 42514796047770330626689037)
                  ·
                    refine ⟨15943048517913873985008389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42514796047770330626689037 15943048517913873985008389)
                    ·
                      refine ⟨2989321597108851372189073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15943048517913873985008389 2989321597108851372189073)
                      ·
                        rfl

theorem cell23_5821683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_5821683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821683 prefixEnd_5821683 := by exact prefixLift 5821683
  have htrace : WordTrace (prefixWord ++ tailWord_5821683) baseStart_5821683 baseEnd_5821683 := by
    simpa [prefixWord, tailWord_5821683, baseEnd_5821683] using wordTrace_append hprefix tailTrace_5821683
  have hstable : (prefixWord ++ tailWord_5821683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821683).length < 2 ^ (prefixWord ++ tailWord_5821683).sum := by decide
  have hdescent : baseEnd_5821683 < baseStart_5821683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821700 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5821700 : Nat := 118140960795 + 5821700 * 2 ^ 59
def prefixEnd_5821700 : Nat := 4983230072969 + 3 ^ 40 * 5821700 * 2
def baseEnd_5821700 : Nat := 2989330326279977805676495

theorem tailTrace_5821700 : CollatzResearch.WordTrace tailWord_5821700 prefixEnd_5821700 2989330326279977805676495 := by
  unfold tailWord_5821700
  simp only [CollatzResearch.WordTrace]
  refine ⟨106167421504491321023727277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141556562005988428031636369 106167421504491321023727277)
  ·
    refine ⟨39812783064184245383897729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106167421504491321023727277 39812783064184245383897729)
    ·
      refine ⟨29859587298138184037923297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39812783064184245383897729 29859587298138184037923297)
      ·
        refine ⟨22394690473603638028442473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29859587298138184037923297 22394690473603638028442473)
        ·
          refine ⟨16796017855202728521331855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22394690473603638028442473 16796017855202728521331855)
          ·
            refine ⟨25194026782804092781997783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796017855202728521331855 25194026782804092781997783)
            ·
              refine ⟨37791040174206139172996675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25194026782804092781997783 37791040174206139172996675)
              ·
                refine ⟨56686560261309208759495013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37791040174206139172996675 56686560261309208759495013)
                ·
                  refine ⟨10628730048995476642405315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56686560261309208759495013 10628730048995476642405315)
                  ·
                    refine ⟨15943095073493214963607973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10628730048995476642405315 15943095073493214963607973)
                    ·
                      refine ⟨2989330326279977805676495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15943095073493214963607973 2989330326279977805676495)
                      ·
                        rfl

theorem cell23_5821700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5821700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821700 prefixEnd_5821700 := by exact prefixLift 5821700
  have htrace : WordTrace (prefixWord ++ tailWord_5821700) baseStart_5821700 baseEnd_5821700 := by
    simpa [prefixWord, tailWord_5821700, baseEnd_5821700] using wordTrace_append hprefix tailTrace_5821700
  have hstable : (prefixWord ++ tailWord_5821700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821700).length < 2 ^ (prefixWord ++ tailWord_5821700).sum := by decide
  have hdescent : baseEnd_5821700 < baseStart_5821700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821761 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5821761 : Nat := 118140960795 + 5821761 * 2 ^ 59
def prefixEnd_5821761 : Nat := 4983230072969 + 3 ^ 40 * 5821761 * 2
def baseEnd_5821761 : Nat := 996453882866634022337905

theorem tailTrace_5821761 : CollatzResearch.WordTrace tailWord_5821761 prefixEnd_5821761 996453882866634022337905 := by
  unfold tailWord_5821761
  simp only [CollatzResearch.WordTrace]
  refine ⟨212337067861761649465425137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141558045241174432976950091 212337067861761649465425137)
  ·
    refine ⟨159252800896321237099068853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212337067861761649465425137 159252800896321237099068853)
    ·
      refine ⟨14929950084030115978037705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159252800896321237099068853 14929950084030115978037705)
      ·
        refine ⟨11197462563022586983528279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14929950084030115978037705 11197462563022586983528279)
        ·
          refine ⟨16796193844533880475292419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197462563022586983528279 16796193844533880475292419)
          ·
            refine ⟨25194290766800820712938629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796193844533880475292419 25194290766800820712938629)
            ·
              refine ⟨4723929518775153883675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25194290766800820712938629 4723929518775153883675993)
              ·
                refine ⟨3542947139081365412756995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4723929518775153883675993 3542947139081365412756995)
                ·
                  refine ⟨5314420708622048119135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542947139081365412756995 5314420708622048119135493)
                  ·
                    refine ⟨996453882866634022337905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314420708622048119135493 996453882866634022337905)
                    ·
                      rfl

theorem cell23_5821761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5821761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821761 prefixEnd_5821761 := by exact prefixLift 5821761
  have htrace : WordTrace (prefixWord ++ tailWord_5821761) baseStart_5821761 baseEnd_5821761 := by
    simpa [prefixWord, tailWord_5821761, baseEnd_5821761] using wordTrace_append hprefix tailTrace_5821761
  have hstable : (prefixWord ++ tailWord_5821761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821761).length < 2 ^ (prefixWord ++ tailWord_5821761).sum := by decide
  have hdescent : baseEnd_5821761 < baseStart_5821761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821804 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_5821804 : Nat := 118140960795 + 5821804 * 2 ^ 59
def prefixEnd_5821804 : Nat := 4983230072969 + 3 ^ 40 * 5821804 * 2
def baseEnd_5821804 : Nat := 996461242756015132925339

theorem tailTrace_5821804 : CollatzResearch.WordTrace tailWord_5821804 prefixEnd_5821804 996461242756015132925339 := by
  unfold tailWord_5821804
  simp only [CollatzResearch.WordTrace]
  refine ⟨106169318100302933904620233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141559090800403911872826977 106169318100302933904620233)
  ·
    refine ⟨79626988575227200428465175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106169318100302933904620233 79626988575227200428465175)
    ·
      refine ⟨119440482862840800642697763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79626988575227200428465175 119440482862840800642697763)
      ·
        refine ⟨179160724294261200964046645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119440482862840800642697763 179160724294261200964046645)
        ·
          refine ⟨16796317902586987590379373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179160724294261200964046645 16796317902586987590379373)
          ·
            refine ⟨6298619213470120346392265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16796317902586987590379373 6298619213470120346392265)
            ·
              refine ⟨4723964410102590259794199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6298619213470120346392265 4723964410102590259794199)
              ·
                refine ⟨7085946615153885389691299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723964410102590259794199 7085946615153885389691299)
                ·
                  refine ⟨10628919922730828084536949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085946615153885389691299 10628919922730828084536949)
                  ·
                    refine ⟨996461242756015132925339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10628919922730828084536949 996461242756015132925339)
                    ·
                      rfl

theorem cell23_5821804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_5821804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821804 prefixEnd_5821804 := by exact prefixLift 5821804
  have htrace : WordTrace (prefixWord ++ tailWord_5821804) baseStart_5821804 baseEnd_5821804 := by
    simpa [prefixWord, tailWord_5821804, baseEnd_5821804] using wordTrace_append hprefix tailTrace_5821804
  have hstable : (prefixWord ++ tailWord_5821804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821804).length < 2 ^ (prefixWord ++ tailWord_5821804).sum := by decide
  have hdescent : baseEnd_5821804 < baseStart_5821804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821807 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 5, 2, 2]
def baseStart_5821807 : Nat := 118140960795 + 5821807 * 2 ^ 59
def prefixEnd_5821807 : Nat := 4983230072969 + 3 ^ 40 * 5821807 * 2
def baseEnd_5821807 : Nat := 2989385268710008887038503

theorem tailTrace_5821807 : CollatzResearch.WordTrace tailWord_5821807 prefixEnd_5821807 2989385268710008887038503 := by
  unfold tailWord_5821807
  simp only [CollatzResearch.WordTrace]
  refine ⟨212338745619594999321599675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141559163746396666214399783 212338745619594999321599675)
  ·
    refine ⟨318508118429392498982399513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212338745619594999321599675 318508118429392498982399513)
    ·
      refine ⟨238881088822044374236799635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318508118429392498982399513 238881088822044374236799635)
      ·
        refine ⟨358321633233066561355199453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238881088822044374236799635 358321633233066561355199453)
        ·
          refine ⟨134370612462399960508199795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358321633233066561355199453 134370612462399960508199795)
          ·
            refine ⟨201555918693599940762299693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134370612462399960508199795 201555918693599940762299693)
            ·
              refine ⟨75583469510099977785862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201555918693599940762299693 75583469510099977785862385)
              ·
                refine ⟨56687602132574983339396789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75583469510099977785862385 56687602132574983339396789)
                ·
                  refine ⟨5314462699928904688068449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56687602132574983339396789 5314462699928904688068449)
                  ·
                    refine ⟨3985847024946678516051337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314462699928904688068449 3985847024946678516051337)
                    ·
                      refine ⟨2989385268710008887038503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985847024946678516051337 2989385268710008887038503)
                      ·
                        rfl

theorem cell23_5821807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 2, 2].length) (baseStart_5821807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821807 prefixEnd_5821807 := by exact prefixLift 5821807
  have htrace : WordTrace (prefixWord ++ tailWord_5821807) baseStart_5821807 baseEnd_5821807 := by
    simpa [prefixWord, tailWord_5821807, baseEnd_5821807] using wordTrace_append hprefix tailTrace_5821807
  have hstable : (prefixWord ++ tailWord_5821807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821807).length < 2 ^ (prefixWord ++ tailWord_5821807).sum := by decide
  have hdescent : baseEnd_5821807 < baseStart_5821807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821810 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_5821810 : Nat := 118140960795 + 5821810 * 2 ^ 59
def prefixEnd_5821810 : Nat := 4983230072969 + 3 ^ 40 * 5821810 * 2
def baseEnd_5821810 : Nat := 2989386809151972375300989

theorem tailTrace_5821810 : CollatzResearch.WordTrace tailWord_5821810 prefixEnd_5821810 2989386809151972375300989 := by
  unfold tailWord_5821810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53084713759646032708489721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141559236692389420555972589 53084713759646032708489721)
  ·
    refine ⟨39813535319734524531367291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53084713759646032708489721 39813535319734524531367291)
    ·
      refine ⟨59720302979601786797050937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39813535319734524531367291 59720302979601786797050937)
      ·
        refine ⟨44790227234701340097788203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59720302979601786797050937 44790227234701340097788203)
        ·
          refine ⟨67185340852052010146682305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44790227234701340097788203 67185340852052010146682305)
          ·
            refine ⟨50389005639039007610011729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67185340852052010146682305 50389005639039007610011729)
            ·
              refine ⟨37791754229279255707508797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50389005639039007610011729 37791754229279255707508797)
              ·
                refine ⟨14171907835979720890315799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37791754229279255707508797 14171907835979720890315799)
                ·
                  refine ⟨21257861753969581335473699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14171907835979720890315799 21257861753969581335473699)
                  ·
                    refine ⟨31886792630954372003210549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21257861753969581335473699 31886792630954372003210549)
                    ·
                      refine ⟨2989386809151972375300989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31886792630954372003210549 2989386809151972375300989)
                      ·
                        rfl

theorem cell23_5821810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_5821810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821810 prefixEnd_5821810 := by exact prefixLift 5821810
  have htrace : WordTrace (prefixWord ++ tailWord_5821810) baseStart_5821810 baseEnd_5821810 := by
    simpa [prefixWord, tailWord_5821810, baseEnd_5821810] using wordTrace_append hprefix tailTrace_5821810
  have hstable : (prefixWord ++ tailWord_5821810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821810).length < 2 ^ (prefixWord ++ tailWord_5821810).sum := by decide
  have hdescent : baseEnd_5821810 < baseStart_5821810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821817 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_5821817 : Nat := 118140960795 + 5821817 * 2 ^ 59
def prefixEnd_5821817 : Nat := 4983230072969 + 3 ^ 40 * 5821817 * 2
def baseEnd_5821817 : Nat := 996463467838851282637819

theorem tailTrace_5821817 : CollatzResearch.WordTrace tailWord_5821817 prefixEnd_5821817 996463467838851282637819 := by
  unfold tailWord_5821817
  simp only [CollatzResearch.WordTrace]
  refine ⟨212339110349558771029463705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141559406899705847352975803 212339110349558771029463705)
  ·
    refine ⟨159254332762169078272097779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212339110349558771029463705 159254332762169078272097779)
    ·
      refine ⟨238881499143253617408146669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159254332762169078272097779 238881499143253617408146669)
      ·
        refine ⟨89580562178720106528055001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238881499143253617408146669 89580562178720106528055001)
        ·
          refine ⟨67185421634040079896041251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89580562178720106528055001 67185421634040079896041251)
          ·
            refine ⟨100778132451060119844061877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67185421634040079896041251 100778132451060119844061877)
            ·
              refine ⟨9447949917286886235380801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100778132451060119844061877 9447949917286886235380801)
              ·
                refine ⟨7085962437965164676535601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9447949917286886235380801 7085962437965164676535601)
                ·
                  refine ⟨5314471828473873507401701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085962437965164676535601 5314471828473873507401701)
                  ·
                    refine ⟨996463467838851282637819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314471828473873507401701 996463467838851282637819)
                    ·
                      rfl

theorem cell23_5821817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_5821817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821817 prefixEnd_5821817 := by exact prefixLift 5821817
  have htrace : WordTrace (prefixWord ++ tailWord_5821817) baseStart_5821817 baseEnd_5821817 := by
    simpa [prefixWord, tailWord_5821817, baseEnd_5821817] using wordTrace_append hprefix tailTrace_5821817
  have hstable : (prefixWord ++ tailWord_5821817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821817).length < 2 ^ (prefixWord ++ tailWord_5821817).sum := by decide
  have hdescent : baseEnd_5821817 < baseStart_5821817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821844 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5821844 : Nat := 118140960795 + 5821844 * 2 ^ 59
def prefixEnd_5821844 : Nat := 4983230072969 + 3 ^ 40 * 5821844 * 2
def baseEnd_5821844 : Nat := 2989404267494225242275833

theorem tailTrace_5821844 : CollatzResearch.WordTrace tailWord_5821844 prefixEnd_5821844 2989404267494225242275833 := by
  unfold tailWord_5821844
  simp only [CollatzResearch.WordTrace]
  refine ⟨106170047560230477320348293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141560063413640636427131057 106170047560230477320348293)
  ·
    refine ⟨19906883917543214497565305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106170047560230477320348293 19906883917543214497565305)
    ·
      refine ⟨14930162938157410873173979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19906883917543214497565305 14930162938157410873173979)
      ·
        refine ⟨22395244407236116309760969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14930162938157410873173979 22395244407236116309760969)
        ·
          refine ⟨16796433305427087232320727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22395244407236116309760969 16796433305427087232320727)
          ·
            refine ⟨25194649958140630848481091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16796433305427087232320727 25194649958140630848481091)
            ·
              refine ⟨37791974937210946272721637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25194649958140630848481091 37791974937210946272721637)
              ·
                refine ⟨7085995300727052426135307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37791974937210946272721637 7085995300727052426135307)
                ·
                  refine ⟨10628992951090578639202961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085995300727052426135307 10628992951090578639202961)
                  ·
                    refine ⟨7971744713317933979402221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10628992951090578639202961 7971744713317933979402221)
                    ·
                      refine ⟨2989404267494225242275833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971744713317933979402221 2989404267494225242275833)
                      ·
                        rfl

theorem cell23_5821844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5821844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821844 prefixEnd_5821844 := by exact prefixLift 5821844
  have htrace : WordTrace (prefixWord ++ tailWord_5821844) baseStart_5821844 baseEnd_5821844 := by
    simpa [prefixWord, tailWord_5821844, baseEnd_5821844] using wordTrace_append hprefix tailTrace_5821844
  have hstable : (prefixWord ++ tailWord_5821844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821844).length < 2 ^ (prefixWord ++ tailWord_5821844).sum := by decide
  have hdescent : baseEnd_5821844 < baseStart_5821844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821858 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_5821858 : Nat := 118140960795 + 5821858 * 2 ^ 59
def prefixEnd_5821858 : Nat := 4983230072969 + 3 ^ 40 * 5821858 * 2
def baseEnd_5821858 : Nat := 2989411456223388187500769

theorem tailTrace_5821858 : CollatzResearch.WordTrace tailWord_5821858 prefixEnd_5821858 2989411456223388187500769 := by
  unfold tailWord_5821858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53085151435602558757926557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141560403828273490021137485 53085151435602558757926557)
  ·
    refine ⟨19906931788350959534222459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53085151435602558757926557 19906931788350959534222459)
    ·
      refine ⟨29860397682526439301333689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19906931788350959534222459 29860397682526439301333689)
      ·
        refine ⟨22395298261894829476000267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29860397682526439301333689 22395298261894829476000267)
        ·
          refine ⟨33592947392842244214000401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22395298261894829476000267 33592947392842244214000401)
          ·
            refine ⟨25194710544631683160500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33592947392842244214000401 25194710544631683160500301)
            ·
              refine ⟨9448016454236881185187613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25194710544631683160500301 9448016454236881185187613)
              ·
                refine ⟨3543006170338830444445355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9448016454236881185187613 3543006170338830444445355)
                ·
                  refine ⟨5314509255508245666668033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543006170338830444445355 5314509255508245666668033)
                  ·
                    refine ⟨3985881941631184250001025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314509255508245666668033 3985881941631184250001025)
                    ·
                      refine ⟨2989411456223388187500769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985881941631184250001025 2989411456223388187500769)
                      ·
                        rfl

theorem cell23_5821858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_5821858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821858 prefixEnd_5821858 := by exact prefixLift 5821858
  have htrace : WordTrace (prefixWord ++ tailWord_5821858) baseStart_5821858 baseEnd_5821858 := by
    simpa [prefixWord, tailWord_5821858, baseEnd_5821858] using wordTrace_append hprefix tailTrace_5821858
  have hstable : (prefixWord ++ tailWord_5821858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821858).length < 2 ^ (prefixWord ++ tailWord_5821858).sum := by decide
  have hdescent : baseEnd_5821858 < baseStart_5821858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821864 : List Nat := [2, 1, 6, 1, 3, 1, 9]
def baseStart_5821864 : Nat := 118140960795 + 5821864 * 2 ^ 59
def prefixEnd_5821864 : Nat := 4983230072969 + 3 ^ 40 * 5821864 * 2
def baseEnd_5821864 : Nat := 36906352309966853876861

theorem tailTrace_5821864 : CollatzResearch.WordTrace tailWord_5821864 prefixEnd_5821864 36906352309966853876861 := by
  unfold tailWord_5821864
  simp only [CollatzResearch.WordTrace]
  refine ⟨106170412290194249028212323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141560549720258998704283097 106170412290194249028212323)
  ·
    refine ⟨159255618435291373542318485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106170412290194249028212323 159255618435291373542318485)
    ·
      refine ⟨7465107114154283134796179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159255618435291373542318485 7465107114154283134796179)
      ·
        refine ⟨11197660671231424702194269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465107114154283134796179 11197660671231424702194269)
        ·
          refine ⟨4199122751711784263322851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11197660671231424702194269 4199122751711784263322851)
          ·
            refine ⟨6298684127567676394984277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199122751711784263322851 6298684127567676394984277)
            ·
              refine ⟨36906352309966853876861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6298684127567676394984277 36906352309966853876861)
              ·
                rfl

theorem cell23_5821864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 9].length) (baseStart_5821864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821864 prefixEnd_5821864 := by exact prefixLift 5821864
  have htrace : WordTrace (prefixWord ++ tailWord_5821864) baseStart_5821864 baseEnd_5821864 := by
    simpa [prefixWord, tailWord_5821864, baseEnd_5821864] using wordTrace_append hprefix tailTrace_5821864
  have hstable : (prefixWord ++ tailWord_5821864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821864).length < 2 ^ (prefixWord ++ tailWord_5821864).sum := by decide
  have hdescent : baseEnd_5821864 < baseStart_5821864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821897 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 4, 2]
def baseStart_5821897 : Nat := 118140960795 + 5821897 * 2 ^ 59
def prefixEnd_5821897 : Nat := 4983230072969 + 3 ^ 40 * 5821897 * 2
def baseEnd_5821897 : Nat := 2989431481968913534913089

theorem tailTrace_5821897 : CollatzResearch.WordTrace tailWord_5821897 prefixEnd_5821897 2989431481968913534913089 := by
  unfold tailWord_5821897
  simp only [CollatzResearch.WordTrace]
  refine ⟨212342028189268944692375945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141561352126179296461583963 212342028189268944692375945)
  ·
    refine ⟨159256521141951708519281959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212342028189268944692375945 159256521141951708519281959)
    ·
      refine ⟨238884781712927562778922939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159256521141951708519281959 238884781712927562778922939)
      ·
        refine ⟨358327172569391344168384409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238884781712927562778922939 358327172569391344168384409)
        ·
          refine ⟨268745379427043508126288307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358327172569391344168384409 268745379427043508126288307)
          ·
            refine ⟨403118069140565262189432461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268745379427043508126288307 403118069140565262189432461)
            ·
              refine ⟨151169275927711973321037173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403118069140565262189432461 151169275927711973321037173)
              ·
                refine ⟨14172119618222997498847235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151169275927711973321037173 14172119618222997498847235)
                ·
                  refine ⟨21258179427334496248270853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14172119618222997498847235 21258179427334496248270853)
                  ·
                    refine ⟨3985908642625218046550785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21258179427334496248270853 3985908642625218046550785)
                    ·
                      refine ⟨2989431481968913534913089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985908642625218046550785 2989431481968913534913089)
                      ·
                        rfl

theorem cell23_5821897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 4, 2].length) (baseStart_5821897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821897 prefixEnd_5821897 := by exact prefixLift 5821897
  have htrace : WordTrace (prefixWord ++ tailWord_5821897) baseStart_5821897 baseEnd_5821897 := by
    simpa [prefixWord, tailWord_5821897, baseEnd_5821897] using wordTrace_append hprefix tailTrace_5821897
  have hstable : (prefixWord ++ tailWord_5821897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821897).length < 2 ^ (prefixWord ++ tailWord_5821897).sum := by decide
  have hdescent : baseEnd_5821897 < baseStart_5821897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821914 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_5821914 : Nat := 118140960795 + 5821914 * 2 ^ 59
def prefixEnd_5821914 : Nat := 4983230072969 + 3 ^ 40 * 5821914 * 2
def baseEnd_5821914 : Nat := 2989440211140039968400511

theorem tailTrace_5821914 : CollatzResearch.WordTrace tailWord_5821914 prefixEnd_5821914 2989440211140039968400511 := by
  unfold tailWord_5821914
  simp only [CollatzResearch.WordTrace]
  refine ⟨53085662057551839148936199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141561765486804904397163197 53085662057551839148936199)
  ·
    refine ⟨79628493086327758723404299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53085662057551839148936199 79628493086327758723404299)
    ·
      refine ⟨119442739629491638085106449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79628493086327758723404299 119442739629491638085106449)
      ·
        refine ⟨89582054722118728563829837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119442739629491638085106449 89582054722118728563829837)
        ·
          refine ⟨33593270520794523211436189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89582054722118728563829837 33593270520794523211436189)
          ·
            refine ⟨12597476445297946204288571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33593270520794523211436189 12597476445297946204288571)
            ·
              refine ⟨18896214667946919306432857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597476445297946204288571 18896214667946919306432857)
              ·
                refine ⟨14172161000960189479824643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18896214667946919306432857 14172161000960189479824643)
                ·
                  refine ⟨21258241501440284219736965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14172161000960189479824643 21258241501440284219736965)
                  ·
                    refine ⟨3985920281520053291200681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21258241501440284219736965 3985920281520053291200681)
                    ·
                      refine ⟨2989440211140039968400511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985920281520053291200681 2989440211140039968400511)
                      ·
                        rfl

theorem cell23_5821914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_5821914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821914 prefixEnd_5821914 := by exact prefixLift 5821914
  have htrace : WordTrace (prefixWord ++ tailWord_5821914) baseStart_5821914 baseEnd_5821914 := by
    simpa [prefixWord, tailWord_5821914, baseEnd_5821914] using wordTrace_append hprefix tailTrace_5821914
  have hstable : (prefixWord ++ tailWord_5821914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821914).length < 2 ^ (prefixWord ++ tailWord_5821914).sum := by decide
  have hdescent : baseEnd_5821914 < baseStart_5821914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821917 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5821917 : Nat := 118140960795 + 5821917 * 2 ^ 59
def prefixEnd_5821917 : Nat := 4983230072969 + 3 ^ 40 * 5821917 * 2
def baseEnd_5821917 : Nat := 2989441751582003456662997

theorem tailTrace_5821917 : CollatzResearch.WordTrace tailWord_5821917 prefixEnd_5821917 2989441751582003456662997 := by
  unfold tailWord_5821917
  simp only [CollatzResearch.WordTrace]
  refine ⟨212342757649196488108104005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141561838432797658738736003 212342757649196488108104005)
  ·
    refine ⟨39814267059224341520269501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212342757649196488108104005 39814267059224341520269501)
    ·
      refine ⟨14930350147209128070101063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39814267059224341520269501 14930350147209128070101063)
      ·
        refine ⟨22395525220813692105151595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14930350147209128070101063 22395525220813692105151595)
        ·
          refine ⟨33593287831220538157727393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22395525220813692105151595 33593287831220538157727393)
          ·
            refine ⟨25194965873415403618295545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33593287831220538157727393 25194965873415403618295545)
            ·
              refine ⟨18896224405061552713721659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25194965873415403618295545 18896224405061552713721659)
              ·
                refine ⟨28344336607592329070582489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896224405061552713721659 28344336607592329070582489)
                ·
                  refine ⟨21258252455694246802936867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28344336607592329070582489 21258252455694246802936867)
                  ·
                    refine ⟨31887378683541370204405301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21258252455694246802936867 31887378683541370204405301)
                    ·
                      refine ⟨2989441751582003456662997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31887378683541370204405301 2989441751582003456662997)
                      ·
                        rfl

theorem cell23_5821917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5821917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821917 prefixEnd_5821917 := by exact prefixLift 5821917
  have htrace : WordTrace (prefixWord ++ tailWord_5821917) baseStart_5821917 baseEnd_5821917 := by
    simpa [prefixWord, tailWord_5821917, baseEnd_5821917] using wordTrace_append hprefix tailTrace_5821917
  have hstable : (prefixWord ++ tailWord_5821917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821917).length < 2 ^ (prefixWord ++ tailWord_5821917).sum := by decide
  have hdescent : baseEnd_5821917 < baseStart_5821917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821954 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_5821954 : Nat := 118140960795 + 5821954 * 2 ^ 59
def prefixEnd_5821954 : Nat := 4983230072969 + 3 ^ 40 * 5821954 * 2
def baseEnd_5821954 : Nat := 332162305596246645766703

theorem tailTrace_5821954 : CollatzResearch.WordTrace tailWord_5821954 prefixEnd_5821954 332162305596246645766703 := by
  unfold tailWord_5821954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53086026787515610856800229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141562738100041628951467277 53086026787515610856800229)
  ·
    refine ⟨9953630022659177035650043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53086026787515610856800229 9953630022659177035650043)
    ·
      refine ⟨14930445033988765553475065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9953630022659177035650043 14930445033988765553475065)
      ·
        refine ⟨11197833775491574165106299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14930445033988765553475065 11197833775491574165106299)
        ·
          refine ⟨16796750663237361247659449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197833775491574165106299 16796750663237361247659449)
          ·
            refine ⟨12597562997428020935744587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16796750663237361247659449 12597562997428020935744587)
            ·
              refine ⟨18896344496142031403616881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597562997428020935744587 18896344496142031403616881)
              ·
                refine ⟨14172258372106523552712661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18896344496142031403616881 14172258372106523552712661)
                ·
                  refine ⟨332162305596246645766703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14172258372106523552712661 332162305596246645766703)
                  ·
                    rfl

theorem cell23_5821954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_5821954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821954 prefixEnd_5821954 := by exact prefixLift 5821954
  have htrace : WordTrace (prefixWord ++ tailWord_5821954) baseStart_5821954 baseEnd_5821954 := by
    simpa [prefixWord, tailWord_5821954, baseEnd_5821954] using wordTrace_append hprefix tailTrace_5821954
  have hstable : (prefixWord ++ tailWord_5821954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821954).length < 2 ^ (prefixWord ++ tailWord_5821954).sum := by decide
  have hdescent : baseEnd_5821954 < baseStart_5821954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821957 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_5821957 : Nat := 118140960795 + 5821957 * 2 ^ 59
def prefixEnd_5821957 : Nat := 4983230072969 + 3 ^ 40 * 5821957 * 2
def baseEnd_5821957 : Nat := 2989462290808183300162813

theorem tailTrace_5821957 : CollatzResearch.WordTrace tailWord_5821957 prefixEnd_5821957 2989462290808183300162813 := by
  unfold tailWord_5821957
  simp only [CollatzResearch.WordTrace]
  refine ⟨212344216569051574939560125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141562811046034383293040083 212344216569051574939560125)
  ·
    refine ⟨79629081213394340602335047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212344216569051574939560125 79629081213394340602335047)
    ·
      refine ⟨119443621820091510903502571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79629081213394340602335047 119443621820091510903502571)
      ·
        refine ⟨179165432730137266355253857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119443621820091510903502571 179165432730137266355253857)
        ·
          refine ⟨134374074547602949766440393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179165432730137266355253857 134374074547602949766440393)
          ·
            refine ⟨100780555910702212324830295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134374074547602949766440393 100780555910702212324830295)
            ·
              refine ⟨151170833866053318487245443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100780555910702212324830295 151170833866053318487245443)
              ·
                refine ⟨226756250799079977730868165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151170833866053318487245443 226756250799079977730868165)
                ·
                  refine ⟨42516797024827495824537781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226756250799079977730868165 42516797024827495824537781)
                  ·
                    refine ⟨3985949721077577733550417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42516797024827495824537781 3985949721077577733550417)
                    ·
                      refine ⟨2989462290808183300162813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985949721077577733550417 2989462290808183300162813)
                      ·
                        rfl

theorem cell23_5821957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_5821957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821957 prefixEnd_5821957 := by exact prefixLift 5821957
  have htrace : WordTrace (prefixWord ++ tailWord_5821957) baseStart_5821957 baseEnd_5821957 := by
    simpa [prefixWord, tailWord_5821957, baseEnd_5821957] using wordTrace_append hprefix tailTrace_5821957
  have hstable : (prefixWord ++ tailWord_5821957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821957).length < 2 ^ (prefixWord ++ tailWord_5821957).sum := by decide
  have hdescent : baseEnd_5821957 < baseStart_5821957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821960 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5821960 : Nat := 118140960795 + 5821960 * 2 ^ 59
def prefixEnd_5821960 : Nat := 4983230072969 + 3 ^ 40 * 5821960 * 2
def baseEnd_5821960 : Nat := 2989463831250146788425299

theorem tailTrace_5821960 : CollatzResearch.WordTrace tailWord_5821960 prefixEnd_5821960 2989463831250146788425299 := by
  unfold tailWord_5821960
  simp only [CollatzResearch.WordTrace]
  refine ⟨106172162994020353225959667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141562883992027137634612889 106172162994020353225959667)
  ·
    refine ⟨159258244491030529838939501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106172162994020353225959667 159258244491030529838939501)
    ·
      refine ⟨59721841684136448689602313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159258244491030529838939501 59721841684136448689602313)
      ·
        refine ⟨44791381263102336517201735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59721841684136448689602313 44791381263102336517201735)
        ·
          refine ⟨67187071894653504775802603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44791381263102336517201735 67187071894653504775802603)
          ·
            refine ⟨100780607841980257163703905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67187071894653504775802603 100780607841980257163703905)
            ·
              refine ⟨75585455881485192872777929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100780607841980257163703905 75585455881485192872777929)
              ·
                refine ⟨56689091911113894654583447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75585455881485192872777929 56689091911113894654583447)
                ·
                  refine ⟨85033637866670841981875171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56689091911113894654583447 85033637866670841981875171)
                  ·
                    refine ⟨127550456800006262972812757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85033637866670841981875171 127550456800006262972812757)
                    ·
                      refine ⟨2989463831250146788425299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127550456800006262972812757 2989463831250146788425299)
                      ·
                        rfl

theorem cell23_5821960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5821960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821960 prefixEnd_5821960 := by exact prefixLift 5821960
  have htrace : WordTrace (prefixWord ++ tailWord_5821960) baseStart_5821960 baseEnd_5821960 := by
    simpa [prefixWord, tailWord_5821960, baseEnd_5821960] using wordTrace_append hprefix tailTrace_5821960
  have hstable : (prefixWord ++ tailWord_5821960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821960).length < 2 ^ (prefixWord ++ tailWord_5821960).sum := by decide
  have hdescent : baseEnd_5821960 < baseStart_5821960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5821982 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5821982 : Nat := 118140960795 + 5821982 * 2 ^ 59
def prefixEnd_5821982 : Nat := 4983230072969 + 3 ^ 40 * 5821982 * 2
def baseEnd_5821982 : Nat := 2989475127824545702350199

theorem tailTrace_5821982 : CollatzResearch.WordTrace tailWord_5821982 prefixEnd_5821982 2989475127824545702350199 := by
  unfold tailWord_5821982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543141049245125526152525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141563418929307336139480133 26543141049245125526152525)
  ·
    refine ⟨9953677893466922072307197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26543141049245125526152525 9953677893466922072307197)
    ·
      refine ⟨3732629210050095777115199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9953677893466922072307197 3732629210050095777115199)
      ·
        refine ⟨5598943815075143665672799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732629210050095777115199 5598943815075143665672799)
        ·
          refine ⟨8398415722612715498509199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598943815075143665672799 8398415722612715498509199)
          ·
            refine ⟨12597623583919073247763799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398415722612715498509199 12597623583919073247763799)
            ·
              refine ⟨18896435375878609871645699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597623583919073247763799 18896435375878609871645699)
              ·
                refine ⟨28344653063817914807468549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896435375878609871645699 28344653063817914807468549)
                ·
                  refine ⟨5314622449465859026400353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28344653063817914807468549 5314622449465859026400353)
                  ·
                    refine ⟨3985966837099394269800265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314622449465859026400353 3985966837099394269800265)
                    ·
                      refine ⟨2989475127824545702350199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3985966837099394269800265 2989475127824545702350199)
                      ·
                        rfl

theorem cell23_5821982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5821982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5821982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5821982 prefixEnd_5821982 := by exact prefixLift 5821982
  have htrace : WordTrace (prefixWord ++ tailWord_5821982) baseStart_5821982 baseEnd_5821982 := by
    simpa [prefixWord, tailWord_5821982, baseEnd_5821982] using wordTrace_append hprefix tailTrace_5821982
  have hstable : (prefixWord ++ tailWord_5821982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5821982).length < 2 ^ (prefixWord ++ tailWord_5821982).sum := by decide
  have hdescent : baseEnd_5821982 < baseStart_5821982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5821982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822000 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_5822000 : Nat := 118140960795 + 5822000 * 2 ^ 59
def prefixEnd_5822000 : Nat := 4983230072969 + 3 ^ 40 * 5822000 * 2
def baseEnd_5822000 : Nat := 2989484370476326631925115

theorem tailTrace_5822000 : CollatzResearch.WordTrace tailWord_5822000 prefixEnd_5822000 2989484370476326631925115 := by
  unfold tailWord_5822000
  simp only [CollatzResearch.WordTrace]
  refine ⟨106172892453947896641687727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141563856605263862188916969 106172892453947896641687727)
  ·
    refine ⟨159259338680921844962531591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106172892453947896641687727 159259338680921844962531591)
    ·
      refine ⟨238889008021382767443797387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159259338680921844962531591 238889008021382767443797387)
      ·
        refine ⟨358333512032074151165696081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238889008021382767443797387 358333512032074151165696081)
        ·
          refine ⟨268750134024055613374272061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358333512032074151165696081 268750134024055613374272061)
          ·
            refine ⟨100781300259020855015352023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268750134024055613374272061 100781300259020855015352023)
            ·
              refine ⟨151171950388531282523028035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100781300259020855015352023 151171950388531282523028035)
              ·
                refine ⟨226757925582796923784542053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151171950388531282523028035 226757925582796923784542053)
                ·
                  refine ⟨42517111046774423209601635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226757925582796923784542053 42517111046774423209601635)
                  ·
                    refine ⟨63775666570161634814402453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42517111046774423209601635 63775666570161634814402453)
                    ·
                      refine ⟨2989484370476326631925115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63775666570161634814402453 2989484370476326631925115)
                      ·
                        rfl

theorem cell23_5822000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_5822000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822000 prefixEnd_5822000 := by exact prefixLift 5822000
  have htrace : WordTrace (prefixWord ++ tailWord_5822000) baseStart_5822000 baseEnd_5822000 := by
    simpa [prefixWord, tailWord_5822000, baseEnd_5822000] using wordTrace_append hprefix tailTrace_5822000
  have hstable : (prefixWord ++ tailWord_5822000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822000).length < 2 ^ (prefixWord ++ tailWord_5822000).sum := by decide
  have hdescent : baseEnd_5822000 < baseStart_5822000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822007 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_5822007 : Nat := 118140960795 + 5822007 * 2 ^ 59
def prefixEnd_5822007 : Nat := 4983230072969 + 3 ^ 40 * 5822007 * 2
def baseEnd_5822007 : Nat := 2989487964840908104537583

theorem tailTrace_5822007 : CollatzResearch.WordTrace tailWord_5822007 prefixEnd_5822007 2989487964840908104537583 := by
  unfold tailWord_5822007
  simp only [CollatzResearch.WordTrace]
  refine ⟨212346040218870433478880275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141564026812580288985920183 212346040218870433478880275)
  ·
    refine ⟨318519060328305650218320413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212346040218870433478880275 318519060328305650218320413)
    ·
      refine ⟨119444647623114618831870155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318519060328305650218320413 119444647623114618831870155)
      ·
        refine ⟨179166971434671928247805233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119444647623114618831870155 179166971434671928247805233)
        ·
          refine ⟨134375228576003946185853925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179166971434671928247805233 134375228576003946185853925)
          ·
            refine ⟨25195355358000739909847611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134375228576003946185853925 25195355358000739909847611)
            ·
              refine ⟨37793033037001109864771417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25195355358000739909847611 37793033037001109864771417)
              ·
                refine ⟨28344774777750832398578563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37793033037001109864771417 28344774777750832398578563)
                ·
                  refine ⟨42517162166626248597867845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28344774777750832398578563 42517162166626248597867845)
                  ·
                    refine ⟨7971967906242421612100221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42517162166626248597867845 7971967906242421612100221)
                    ·
                      refine ⟨2989487964840908104537583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7971967906242421612100221 2989487964840908104537583)
                      ·
                        rfl

theorem cell23_5822007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_5822007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822007 prefixEnd_5822007 := by exact prefixLift 5822007
  have htrace : WordTrace (prefixWord ++ tailWord_5822007) baseStart_5822007 baseEnd_5822007 := by
    simpa [prefixWord, tailWord_5822007, baseEnd_5822007] using wordTrace_append hprefix tailTrace_5822007
  have hstable : (prefixWord ++ tailWord_5822007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822007).length < 2 ^ (prefixWord ++ tailWord_5822007).sum := by decide
  have hdescent : baseEnd_5822007 < baseStart_5822007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822017 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5822017 : Nat := 118140960795 + 5822017 * 2 ^ 59
def prefixEnd_5822017 : Nat := 4983230072969 + 3 ^ 40 * 5822017 * 2
def baseEnd_5822017 : Nat := 2989493099647453065412537

theorem tailTrace_5822017 : CollatzResearch.WordTrace tailWord_5822017 prefixEnd_5822017 2989493099647453065412537 := by
  unfold tailWord_5822017
  simp only [CollatzResearch.WordTrace]
  refine ⟨212346404948834205186744305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141564269965889470124496203 212346404948834205186744305)
  ·
    refine ⟨159259803711625653890058229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212346404948834205186744305 159259803711625653890058229)
    ·
      refine ⟨14930606597964905052192959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159259803711625653890058229 14930606597964905052192959)
      ·
        refine ⟨22395909896947357578289439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14930606597964905052192959 22395909896947357578289439)
        ·
          refine ⟨33593864845421036367434159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22395909896947357578289439 33593864845421036367434159)
          ·
            refine ⟨50390797268131554551151239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33593864845421036367434159 50390797268131554551151239)
            ·
              refine ⟨75586195902197331826726859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50390797268131554551151239 75586195902197331826726859)
              ·
                refine ⟨113379293853295997740090289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75586195902197331826726859 113379293853295997740090289)
                ·
                  refine ⟨85034470389971998305067717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113379293853295997740090289 85034470389971998305067717)
                  ·
                    refine ⟨15943963198119749682200197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85034470389971998305067717 15943963198119749682200197)
                    ·
                      refine ⟨2989493099647453065412537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15943963198119749682200197 2989493099647453065412537)
                      ·
                        rfl

theorem cell23_5822017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5822017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822017 prefixEnd_5822017 := by exact prefixLift 5822017
  have htrace : WordTrace (prefixWord ++ tailWord_5822017) baseStart_5822017 baseEnd_5822017 := by
    simpa [prefixWord, tailWord_5822017, baseEnd_5822017] using wordTrace_append hprefix tailTrace_5822017
  have hstable : (prefixWord ++ tailWord_5822017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822017).length < 2 ^ (prefixWord ++ tailWord_5822017).sum := by decide
  have hdescent : baseEnd_5822017 < baseStart_5822017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822081 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5822081 : Nat := 118140960795 + 5822081 * 2 ^ 59
def prefixEnd_5822081 : Nat := 4983230072969 + 3 ^ 40 * 5822081 * 2
def baseEnd_5822081 : Nat := 2989525962409340815012243

theorem tailTrace_5822081 : CollatzResearch.WordTrace tailWord_5822081 prefixEnd_5822081 2989525962409340815012243 := by
  unfold tailWord_5822081
  simp only [CollatzResearch.WordTrace]
  refine ⟨212348739220602344117074097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141565826147068229411382731 212348739220602344117074097)
  ·
    refine ⟨159261554415451758087805573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212348739220602344117074097 159261554415451758087805573)
    ·
      refine ⟨29861541452897204641463545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159261554415451758087805573 29861541452897204641463545)
      ·
        refine ⟨22396156089672903481097659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29861541452897204641463545 22396156089672903481097659)
        ·
          refine ⟨33594234134509355221646489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22396156089672903481097659 33594234134509355221646489)
          ·
            refine ⟨25195675600882016416234867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33594234134509355221646489 25195675600882016416234867)
            ·
              refine ⟨37793513401323024624352301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25195675600882016416234867 37793513401323024624352301)
              ·
                refine ⟨14172567525496134234132113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37793513401323024624352301 14172567525496134234132113)
                ·
                  refine ⟨10629425644122100675599085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14172567525496134234132113 10629425644122100675599085)
                  ·
                    refine ⟨3986034616545787753349657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10629425644122100675599085 3986034616545787753349657)
                    ·
                      refine ⟨2989525962409340815012243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986034616545787753349657 2989525962409340815012243)
                      ·
                        rfl

theorem cell23_5822081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5822081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822081 prefixEnd_5822081 := by exact prefixLift 5822081
  have htrace : WordTrace (prefixWord ++ tailWord_5822081) baseStart_5822081 baseEnd_5822081 := by
    simpa [prefixWord, tailWord_5822081, baseEnd_5822081] using wordTrace_append hprefix tailTrace_5822081
  have hstable : (prefixWord ++ tailWord_5822081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822081).length < 2 ^ (prefixWord ++ tailWord_5822081).sum := by decide
  have hdescent : baseEnd_5822081 < baseStart_5822081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822087 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 6]
def baseStart_5822087 : Nat := 118140960795 + 5822087 * 2 ^ 59
def prefixEnd_5822087 : Nat := 4983230072969 + 3 ^ 40 * 5822087 * 2
def baseEnd_5822087 : Nat := 996509681097755930512405

theorem tailTrace_5822087 : CollatzResearch.WordTrace tailWord_5822087 prefixEnd_5822087 996509681097755930512405 := by
  unfold tailWord_5822087
  simp only [CollatzResearch.WordTrace]
  refine ⟨212348958058580607141792515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141565972039053738094528343 212348958058580607141792515)
  ·
    refine ⟨318523437087870910712688773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212348958058580607141792515 318523437087870910712688773)
    ·
      refine ⟨59723144453975795758629145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318523437087870910712688773 59723144453975795758629145)
      ·
        refine ⟨44792358340481846818971859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59723144453975795758629145 44792358340481846818971859)
        ·
          refine ⟨67188537510722770228457789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44792358340481846818971859 67188537510722770228457789)
          ·
            refine ⟨25195701566521038835671671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67188537510722770228457789 25195701566521038835671671)
            ·
              refine ⟨37793552349781558253507507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25195701566521038835671671 37793552349781558253507507)
              ·
                refine ⟨56690328524672337380261261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37793552349781558253507507 56690328524672337380261261)
                ·
                  refine ⟨21258873196752126517597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56690328524672337380261261 21258873196752126517597973)
                  ·
                    refine ⟨996509681097755930512405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21258873196752126517597973 996509681097755930512405)
                    ·
                      rfl

theorem cell23_5822087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_5822087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822087 prefixEnd_5822087 := by exact prefixLift 5822087
  have htrace : WordTrace (prefixWord ++ tailWord_5822087) baseStart_5822087 baseEnd_5822087 := by
    simpa [prefixWord, tailWord_5822087, baseEnd_5822087] using wordTrace_append hprefix tailTrace_5822087
  have hstable : (prefixWord ++ tailWord_5822087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822087).length < 2 ^ (prefixWord ++ tailWord_5822087).sum := by decide
  have hdescent : baseEnd_5822087 < baseStart_5822087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_5822097 : Nat := 118140960795 + 5822097 * 2 ^ 59
def prefixEnd_5822097 : Nat := 4983230072969 + 3 ^ 40 * 5822097 * 2
def baseEnd_5822097 : Nat := 2989534178099812752412169

theorem tailTrace_5822097 : CollatzResearch.WordTrace tailWord_5822097 prefixEnd_5822097 2989534178099812752412169 := by
  unfold tailWord_5822097
  simp only [CollatzResearch.WordTrace]
  refine ⟨212349322788544378849656545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141566215192362919233104363 212349322788544378849656545)
  ·
    refine ⟨159261992091408284137242409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212349322788544378849656545 159261992091408284137242409)
    ·
      refine ⟨119446494068556213102931807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159261992091408284137242409 119446494068556213102931807)
      ·
        refine ⟨179169741102834319654397711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119446494068556213102931807 179169741102834319654397711)
        ·
          refine ⟨268754611654251479481596567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179169741102834319654397711 268754611654251479481596567)
          ·
            refine ⟨403131917481377219222394851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268754611654251479481596567 403131917481377219222394851)
            ·
              refine ⟨604697876222065828833592277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403131917481377219222394851 604697876222065828833592277)
              ·
                refine ⟨14172606473954667863287319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 604697876222065828833592277 14172606473954667863287319)
                ·
                  refine ⟨21258909710932001794930979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14172606473954667863287319 21258909710932001794930979)
                  ·
                    refine ⟨31888364566398002692396469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21258909710932001794930979 31888364566398002692396469)
                    ·
                      refine ⟨2989534178099812752412169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31888364566398002692396469 2989534178099812752412169)
                      ·
                        rfl

theorem cell23_5822097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_5822097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822097 prefixEnd_5822097 := by exact prefixLift 5822097
  have htrace : WordTrace (prefixWord ++ tailWord_5822097) baseStart_5822097 baseEnd_5822097 := by
    simpa [prefixWord, tailWord_5822097, baseEnd_5822097] using wordTrace_append hprefix tailTrace_5822097
  have hstable : (prefixWord ++ tailWord_5822097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822097).length < 2 ^ (prefixWord ++ tailWord_5822097).sum := by decide
  have hdescent : baseEnd_5822097 < baseStart_5822097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822117 : List Nat := [1, 3, 1, 2, 1, 2, 5, 8]
def baseStart_5822117 : Nat := 118140960795 + 5822117 * 2 ^ 59
def prefixEnd_5822117 : Nat := 4983230072969 + 3 ^ 40 * 5822117 * 2
def baseEnd_5822117 : Nat := 110723868433811210154151

theorem tailTrace_5822117 : CollatzResearch.WordTrace tailWord_5822117 prefixEnd_5822117 110723868433811210154151 := by
  unfold tailWord_5822117
  simp only [CollatzResearch.WordTrace]
  refine ⟨212350052248471922265384605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141566701498981281510256403 212350052248471922265384605)
  ·
    refine ⟨79631269593176970849519227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212350052248471922265384605 79631269593176970849519227)
    ·
      refine ⟨119446904389765456274278841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79631269593176970849519227 119446904389765456274278841)
      ·
        refine ⟨89585178292324092205709131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119446904389765456274278841 89585178292324092205709131)
        ·
          refine ⟨134377767438486138308563697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89585178292324092205709131 134377767438486138308563697)
          ·
            refine ⟨100783325578864603731422773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134377767438486138308563697 100783325578864603731422773)
            ·
              refine ⟨9448436773018556599820885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100783325578864603731422773 9448436773018556599820885)
              ·
                refine ⟨110723868433811210154151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9448436773018556599820885 110723868433811210154151)
                ·
                  rfl

theorem cell23_5822117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 8].length) (baseStart_5822117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822117 prefixEnd_5822117 := by exact prefixLift 5822117
  have htrace : WordTrace (prefixWord ++ tailWord_5822117) baseStart_5822117 baseEnd_5822117 := by
    simpa [prefixWord, tailWord_5822117, baseEnd_5822117] using wordTrace_append hprefix tailTrace_5822117
  have hstable : (prefixWord ++ tailWord_5822117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822117).length < 2 ^ (prefixWord ++ tailWord_5822117).sum := by decide
  have hdescent : baseEnd_5822117 < baseStart_5822117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822144 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_5822144 : Nat := 118140960795 + 5822144 * 2 ^ 59
def prefixEnd_5822144 : Nat := 4983230072969 + 3 ^ 40 * 5822144 * 2
def baseEnd_5822144 : Nat := 2989558311690574068524453

theorem tailTrace_5822144 : CollatzResearch.WordTrace tailWord_5822144 prefixEnd_5822144 2989558311690574068524453 := by
  unfold tailWord_5822144
  simp only [CollatzResearch.WordTrace]
  refine ⟨106175518509687052938308743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141567358012916070584411657 106175518509687052938308743)
  ·
    refine ⟨159263277764530579407463115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106175518509687052938308743 159263277764530579407463115)
    ·
      refine ⟨238894916646795869111194673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159263277764530579407463115 238894916646795869111194673)
      ·
        refine ⟨179171187485096901833396005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238894916646795869111194673 179171187485096901833396005)
        ·
          refine ⟨33594597653455669093761751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179171187485096901833396005 33594597653455669093761751)
          ·
            refine ⟨50391896480183503640642627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33594597653455669093761751 50391896480183503640642627)
            ·
              refine ⟨75587844720275255460963941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50391896480183503640642627 75587844720275255460963941)
              ·
                refine ⟨14172720885051610398930739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75587844720275255460963941 14172720885051610398930739)
                ·
                  refine ⟨21259081327577415598396109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14172720885051610398930739 21259081327577415598396109)
                  ·
                    refine ⟨7972155497841530849398541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21259081327577415598396109 7972155497841530849398541)
                    ·
                      refine ⟨2989558311690574068524453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972155497841530849398541 2989558311690574068524453)
                      ·
                        rfl

theorem cell23_5822144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_5822144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822144 prefixEnd_5822144 := by exact prefixLift 5822144
  have htrace : WordTrace (prefixWord ++ tailWord_5822144) baseStart_5822144 baseEnd_5822144 := by
    simpa [prefixWord, tailWord_5822144, baseEnd_5822144] using wordTrace_append hprefix tailTrace_5822144
  have hstable : (prefixWord ++ tailWord_5822144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822144).length < 2 ^ (prefixWord ++ tailWord_5822144).sum := by decide
  have hdescent : baseEnd_5822144 < baseStart_5822144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822161 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_5822161 : Nat := 118140960795 + 5822161 * 2 ^ 59
def prefixEnd_5822161 : Nat := 4983230072969 + 3 ^ 40 * 5822161 * 2
def baseEnd_5822161 : Nat := 2989567040861700502011875

theorem tailTrace_5822161 : CollatzResearch.WordTrace tailWord_5822161 prefixEnd_5822161 2989567040861700502011875 := by
  unfold tailWord_5822161
  simp only [CollatzResearch.WordTrace]
  refine ⟨212351657060312517779986337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141567771373541678519990891 212351657060312517779986337)
  ·
    refine ⟨159263742795234388334989753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212351657060312517779986337 159263742795234388334989753)
    ·
      refine ⟨119447807096425791251242315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159263742795234388334989753 119447807096425791251242315)
      ·
        refine ⟨179171710644638686876863473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119447807096425791251242315 179171710644638686876863473)
        ·
          refine ⟨134378782983479015157647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179171710644638686876863473 134378782983479015157647605)
          ·
            refine ⟨12598010904701157671029463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134378782983479015157647605 12598010904701157671029463)
            ·
              refine ⟨18897016357051736506544195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598010904701157671029463 18897016357051736506544195)
              ·
                refine ⟨28345524535577604759816293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18897016357051736506544195 28345524535577604759816293)
                ·
                  refine ⟨5314785850420800892465555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28345524535577604759816293 5314785850420800892465555)
                  ·
                    refine ⟨7972178775631201338698333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5314785850420800892465555 7972178775631201338698333)
                    ·
                      refine ⟨2989567040861700502011875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972178775631201338698333 2989567040861700502011875)
                      ·
                        rfl

theorem cell23_5822161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_5822161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822161 prefixEnd_5822161 := by exact prefixLift 5822161
  have htrace : WordTrace (prefixWord ++ tailWord_5822161) baseStart_5822161 baseEnd_5822161 := by
    simpa [prefixWord, tailWord_5822161, baseEnd_5822161] using wordTrace_append hprefix tailTrace_5822161
  have hstable : (prefixWord ++ tailWord_5822161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822161).length < 2 ^ (prefixWord ++ tailWord_5822161).sum := by decide
  have hdescent : baseEnd_5822161 < baseStart_5822161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822196 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5822196 : Nat := 118140960795 + 5822196 * 2 ^ 59
def prefixEnd_5822196 : Nat := 4983230072969 + 3 ^ 40 * 5822196 * 2
def baseEnd_5822196 : Nat := 2989585012684607865074215

theorem tailTrace_5822196 : CollatzResearch.WordTrace tailWord_5822196 prefixEnd_5822196 2989585012684607865074215 := by
  unfold tailWord_5822196
  simp only [CollatzResearch.WordTrace]
  refine ⟨106176466807592859378755221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141568622410123812505006961 106176466807592859378755221)
  ·
    refine ⟨4977021881605915283379151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106176466807592859378755221 4977021881605915283379151)
    ·
      refine ⟨7465532822408872925068727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977021881605915283379151 7465532822408872925068727)
      ·
        refine ⟨11198299233613309387603091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465532822408872925068727 11198299233613309387603091)
        ·
          refine ⟨16797448850419964081404637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11198299233613309387603091 16797448850419964081404637)
          ·
            refine ⟨6299043318907486530526739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16797448850419964081404637 6299043318907486530526739)
            ·
              refine ⟨9448564978361229795790109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299043318907486530526739 9448564978361229795790109)
              ·
                refine ⟨3543211866885461173421291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9448564978361229795790109 3543211866885461173421291)
                ·
                  refine ⟨5314817800328191760131937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543211866885461173421291 5314817800328191760131937)
                  ·
                    refine ⟨3986113350246143820098953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314817800328191760131937 3986113350246143820098953)
                    ·
                      refine ⟨2989585012684607865074215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986113350246143820098953 2989585012684607865074215)
                      ·
                        rfl

theorem cell23_5822196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5822196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822196 prefixEnd_5822196 := by exact prefixLift 5822196
  have htrace : WordTrace (prefixWord ++ tailWord_5822196) baseStart_5822196 baseEnd_5822196 := by
    simpa [prefixWord, tailWord_5822196, baseEnd_5822196] using wordTrace_append hprefix tailTrace_5822196
  have hstable : (prefixWord ++ tailWord_5822196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822196).length < 2 ^ (prefixWord ++ tailWord_5822196).sum := by decide
  have hdescent : baseEnd_5822196 < baseStart_5822196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822204 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_5822204 : Nat := 118140960795 + 5822204 * 2 ^ 59
def prefixEnd_5822204 : Nat := 4983230072969 + 3 ^ 40 * 5822204 * 2
def baseEnd_5822204 : Nat := 2989589120529843833774177

theorem tailTrace_5822204 : CollatzResearch.WordTrace tailWord_5822204 prefixEnd_5822204 2989589120529843833774177 := by
  unfold tailWord_5822204
  simp only [CollatzResearch.WordTrace]
  refine ⟨106176612699578368061900833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141568816932771157415867777 106176612699578368061900833)
  ·
    refine ⟨79632459524683776046425625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106176612699578368061900833 79632459524683776046425625)
    ·
      refine ⟨59724344643512832034819219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79632459524683776046425625 59724344643512832034819219)
      ·
        refine ⟨89586516965269248052228829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59724344643512832034819219 89586516965269248052228829)
        ·
          refine ⟨33594943861975968019585811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89586516965269248052228829 33594943861975968019585811)
          ·
            refine ⟨50392415792963952029378717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33594943861975968019585811 50392415792963952029378717)
            ·
              refine ⟨18897155922361482011017019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50392415792963952029378717 18897155922361482011017019)
              ·
                refine ⟨28345733883542223016525529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18897155922361482011017019 28345733883542223016525529)
                ·
                  refine ⟨21259300412656667262394147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28345733883542223016525529 21259300412656667262394147)
                  ·
                    refine ⟨31888950618985000893591221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21259300412656667262394147 31888950618985000893591221)
                    ·
                      refine ⟨2989589120529843833774177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31888950618985000893591221 2989589120529843833774177)
                      ·
                        rfl

theorem cell23_5822204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_5822204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822204 prefixEnd_5822204 := by exact prefixLift 5822204
  have htrace : WordTrace (prefixWord ++ tailWord_5822204) baseStart_5822204 baseEnd_5822204 := by
    simpa [prefixWord, tailWord_5822204, baseEnd_5822204] using wordTrace_append hprefix tailTrace_5822204
  have hstable : (prefixWord ++ tailWord_5822204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822204).length < 2 ^ (prefixWord ++ tailWord_5822204).sum := by decide
  have hdescent : baseEnd_5822204 < baseStart_5822204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822207 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 9]
def baseStart_5822207 : Nat := 118140960795 + 5822207 * 2 ^ 59
def prefixEnd_5822207 : Nat := 4983230072969 + 3 ^ 40 * 5822207 * 2
def baseEnd_5822207 : Nat := 332176740107978591337407

theorem tailTrace_5822207 : CollatzResearch.WordTrace tailWord_5822207 prefixEnd_5822207 332176740107978591337407 := by
  unfold tailWord_5822207
  simp only [CollatzResearch.WordTrace]
  refine ⟨212353334818145867636160875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141568889878763911757440583 212353334818145867636160875)
  ·
    refine ⟨318530002227218801454241313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212353334818145867636160875 318530002227218801454241313)
    ·
      refine ⟨238897501670414101090680985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318530002227218801454241313 238897501670414101090680985)
      ·
        refine ⟨179173126252810575818010739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238897501670414101090680985 179173126252810575818010739)
        ·
          refine ⟨268759689379215863727016109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179173126252810575818010739 268759689379215863727016109)
          ·
            refine ⟨100784883517205948897631041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268759689379215863727016109 100784883517205948897631041)
            ·
              refine ⟨75588662637904461673223281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100784883517205948897631041 75588662637904461673223281)
              ·
                refine ⟨56691496978428346254917461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75588662637904461673223281 56691496978428346254917461)
                ·
                  refine ⟨332176740107978591337407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56691496978428346254917461 332176740107978591337407)
                  ·
                    rfl

theorem cell23_5822207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 9].length) (baseStart_5822207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822207 prefixEnd_5822207 := by exact prefixLift 5822207
  have htrace : WordTrace (prefixWord ++ tailWord_5822207) baseStart_5822207 baseEnd_5822207 := by
    simpa [prefixWord, tailWord_5822207, baseEnd_5822207] using wordTrace_append hprefix tailTrace_5822207
  have hstable : (prefixWord ++ tailWord_5822207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822207).length < 2 ^ (prefixWord ++ tailWord_5822207).sum := by decide
  have hdescent : baseEnd_5822207 < baseStart_5822207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_5822217 : Nat := 118140960795 + 5822217 * 2 ^ 59
def prefixEnd_5822217 : Nat := 4983230072969 + 3 ^ 40 * 5822217 * 2
def baseEnd_5822217 : Nat := 2989595795778352282911617

theorem tailTrace_5822217 : CollatzResearch.WordTrace tailWord_5822217 prefixEnd_5822217 2989595795778352282911617 := by
  unfold tailWord_5822217
  simp only [CollatzResearch.WordTrace]
  refine ⟨212353699548109639344024905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141569133032073092896016603 212353699548109639344024905)
  ·
    refine ⟨159265274661082229508018679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212353699548109639344024905 159265274661082229508018679)
    ·
      refine ⟨238897911991623344262028019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159265274661082229508018679 238897911991623344262028019)
      ·
        refine ⟨358346867987435016393042029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238897911991623344262028019 358346867987435016393042029)
        ·
          refine ⟨134380075495288131147390761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358346867987435016393042029 134380075495288131147390761)
          ·
            refine ⟨100785056621466098360543071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134380075495288131147390761 100785056621466098360543071)
            ·
              refine ⟨151177584932199147540814607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100785056621466098360543071 151177584932199147540814607)
              ·
                refine ⟨226766377398298721311221911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151177584932199147540814607 226766377398298721311221911)
                ·
                  refine ⟨340149566097448081966832867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226766377398298721311221911 340149566097448081966832867)
                  ·
                    refine ⟨510224349146172122950249301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340149566097448081966832867 510224349146172122950249301)
                    ·
                      refine ⟨2989595795778352282911617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 510224349146172122950249301 2989595795778352282911617)
                      ·
                        rfl

theorem cell23_5822217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_5822217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822217 prefixEnd_5822217 := by exact prefixLift 5822217
  have htrace : WordTrace (prefixWord ++ tailWord_5822217) baseStart_5822217 baseEnd_5822217 := by
    simpa [prefixWord, tailWord_5822217, baseEnd_5822217] using wordTrace_append hprefix tailTrace_5822217
  have hstable : (prefixWord ++ tailWord_5822217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822217).length < 2 ^ (prefixWord ++ tailWord_5822217).sum := by decide
  have hdescent : baseEnd_5822217 < baseStart_5822217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822218 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_5822218 : Nat := 118140960795 + 5822218 * 2 ^ 59
def prefixEnd_5822218 : Nat := 4983230072969 + 3 ^ 40 * 5822218 * 2
def baseEnd_5822218 : Nat := 2989596309259006778999113

theorem tailTrace_5822218 : CollatzResearch.WordTrace tailWord_5822218 prefixEnd_5822218 2989596309259006778999113 := by
  unfold tailWord_5822218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53088434005276504128702827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141569157347404011009874205 53088434005276504128702827)
  ·
    refine ⟨79632651007914756193054241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53088434005276504128702827 79632651007914756193054241)
    ·
      refine ⟨59724488255936067144790681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79632651007914756193054241 59724488255936067144790681)
      ·
        refine ⟨44793366191952050358593011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59724488255936067144790681 44793366191952050358593011)
        ·
          refine ⟨67190049287928075537889517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44793366191952050358593011 67190049287928075537889517)
          ·
            refine ⟨25196268482973028326708569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67190049287928075537889517 25196268482973028326708569)
            ·
              refine ⟨18897201362229771245031427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25196268482973028326708569 18897201362229771245031427)
              ·
                refine ⟨28345802043344656867547141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18897201362229771245031427 28345802043344656867547141)
                ·
                  refine ⟨5314837883127123162665089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28345802043344656867547141 5314837883127123162665089)
                  ·
                    refine ⟨3986128412345342371998817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314837883127123162665089 3986128412345342371998817)
                    ·
                      refine ⟨2989596309259006778999113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986128412345342371998817 2989596309259006778999113)
                      ·
                        rfl

theorem cell23_5822218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_5822218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822218 prefixEnd_5822218 := by exact prefixLift 5822218
  have htrace : WordTrace (prefixWord ++ tailWord_5822218) baseStart_5822218 baseEnd_5822218 := by
    simpa [prefixWord, tailWord_5822218, baseEnd_5822218] using wordTrace_append hprefix tailTrace_5822218
  have hstable : (prefixWord ++ tailWord_5822218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822218).length < 2 ^ (prefixWord ++ tailWord_5822218).sum := by decide
  have hdescent : baseEnd_5822218 < baseStart_5822218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822227 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_5822227 : Nat := 118140960795 + 5822227 * 2 ^ 59
def prefixEnd_5822227 : Nat := 4983230072969 + 3 ^ 40 * 5822227 * 2
def baseEnd_5822227 : Nat := 2989600930584897243786571

theorem tailTrace_5822227 : CollatzResearch.WordTrace tailWord_5822227 prefixEnd_5822227 2989600930584897243786571 := by
  unfold tailWord_5822227
  simp only [CollatzResearch.WordTrace]
  refine ⟨212354064278073411051888935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141569376185382274034592623 212354064278073411051888935)
  ·
    refine ⟨318531096417110116577833403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212354064278073411051888935 318531096417110116577833403)
    ·
      refine ⟨477796644625665174866750105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318531096417110116577833403 477796644625665174866750105)
      ·
        refine ⟨358347483469248881150062579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477796644625665174866750105 358347483469248881150062579)
        ·
          refine ⟨537521225203873321725093869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358347483469248881150062579 537521225203873321725093869)
          ·
            refine ⟨201570459451452495646910201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537521225203873321725093869 201570459451452495646910201)
            ·
              refine ⟨151177844588589371735182651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201570459451452495646910201 151177844588589371735182651)
              ·
                refine ⟨226766766882884057602773977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151177844588589371735182651 226766766882884057602773977)
                ·
                  refine ⟨170075075162163043202080483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226766766882884057602773977 170075075162163043202080483)
                  ·
                    refine ⟨255112612743244564803120725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170075075162163043202080483 255112612743244564803120725)
                    ·
                      refine ⟨2989600930584897243786571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 255112612743244564803120725 2989600930584897243786571)
                      ·
                        rfl

theorem cell23_5822227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_5822227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822227 prefixEnd_5822227 := by exact prefixLift 5822227
  have htrace : WordTrace (prefixWord ++ tailWord_5822227) baseStart_5822227 baseEnd_5822227 := by
    simpa [prefixWord, tailWord_5822227, baseEnd_5822227] using wordTrace_append hprefix tailTrace_5822227
  have hstable : (prefixWord ++ tailWord_5822227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822227).length < 2 ^ (prefixWord ++ tailWord_5822227).sum := by decide
  have hdescent : baseEnd_5822227 < baseStart_5822227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822264 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_5822264 : Nat := 118140960795 + 5822264 * 2 ^ 59
def prefixEnd_5822264 : Nat := 4983230072969 + 3 ^ 40 * 5822264 * 2
def baseEnd_5822264 : Nat := 2989619929369113599023901

theorem tailTrace_5822264 : CollatzResearch.WordTrace tailWord_5822264 prefixEnd_5822264 2989619929369113599023901 := by
  unfold tailWord_5822264
  simp only [CollatzResearch.WordTrace]
  refine ⟨106177706889469683185492923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141570275852626244247323897 106177706889469683185492923)
  ·
    refine ⟨159266560334204524778239385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106177706889469683185492923 159266560334204524778239385)
    ·
      refine ⟨119449920250653393583679539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159266560334204524778239385 119449920250653393583679539)
      ·
        refine ⟨179174880375980090375519309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119449920250653393583679539 179174880375980090375519309)
        ·
          refine ⟨67190580140992533890819741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179174880375980090375519309 67190580140992533890819741)
          ·
            refine ⟨25196467552872200209057403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67190580140992533890819741 25196467552872200209057403)
            ·
              refine ⟨37794701329308300313586105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25196467552872200209057403 37794701329308300313586105)
              ·
                refine ⟨28346025996981225235189579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37794701329308300313586105 28346025996981225235189579)
                ·
                  refine ⟨42519038995471837852784369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28346025996981225235189579 42519038995471837852784369)
                  ·
                    refine ⟨31889279246603878389588277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42519038995471837852784369 31889279246603878389588277)
                    ·
                      refine ⟨2989619929369113599023901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31889279246603878389588277 2989619929369113599023901)
                      ·
                        rfl

theorem cell23_5822264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_5822264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822264 prefixEnd_5822264 := by exact prefixLift 5822264
  have htrace : WordTrace (prefixWord ++ tailWord_5822264) baseStart_5822264 baseEnd_5822264 := by
    simpa [prefixWord, tailWord_5822264, baseEnd_5822264] using wordTrace_append hprefix tailTrace_5822264
  have hstable : (prefixWord ++ tailWord_5822264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822264).length < 2 ^ (prefixWord ++ tailWord_5822264).sum := by decide
  have hdescent : baseEnd_5822264 < baseStart_5822264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822311 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_5822311 : Nat := 118140960795 + 5822311 * 2 ^ 59
def prefixEnd_5822311 : Nat := 4983230072969 + 3 ^ 40 * 5822311 * 2
def baseEnd_5822311 : Nat := 2989644062959874915136185

theorem tailTrace_5822311 : CollatzResearch.WordTrace tailWord_5822311 prefixEnd_5822311 2989644062959874915136185 := by
  unfold tailWord_5822311
  simp only [CollatzResearch.WordTrace]
  refine ⟨212357128009769093397946787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141571418673179395598631191 212357128009769093397946787)
  ·
    refine ⟨318535692014653640096920181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212357128009769093397946787 318535692014653640096920181)
    ·
      refine ⟨29862721126373778759086267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 318535692014653640096920181 29862721126373778759086267)
      ·
        refine ⟨44794081689560668138629401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29862721126373778759086267 44794081689560668138629401)
        ·
          refine ⟨33595561267170501103972051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44794081689560668138629401 33595561267170501103972051)
          ·
            refine ⟨50393341900755751655958077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33595561267170501103972051 50393341900755751655958077)
            ·
              refine ⟨18897503212783406870984279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50393341900755751655958077 18897503212783406870984279)
              ·
                refine ⟨28346254819175110306476419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18897503212783406870984279 28346254819175110306476419)
                ·
                  refine ⟨42519382228762665459714629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28346254819175110306476419 42519382228762665459714629)
                  ·
                    refine ⟨7972384167892999773696493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42519382228762665459714629 7972384167892999773696493)
                    ·
                      refine ⟨2989644062959874915136185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972384167892999773696493 2989644062959874915136185)
                      ·
                        rfl

theorem cell23_5822311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_5822311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822311 prefixEnd_5822311 := by exact prefixLift 5822311
  have htrace : WordTrace (prefixWord ++ tailWord_5822311) baseStart_5822311 baseEnd_5822311 := by
    simpa [prefixWord, tailWord_5822311, baseEnd_5822311] using wordTrace_append hprefix tailTrace_5822311
  have hstable : (prefixWord ++ tailWord_5822311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822311).length < 2 ^ (prefixWord ++ tailWord_5822311).sum := by decide
  have hdescent : baseEnd_5822311 < baseStart_5822311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822361 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_5822361 : Nat := 118140960795 + 5822361 * 2 ^ 59
def prefixEnd_5822361 : Nat := 4983230072969 + 3 ^ 40 * 5822361 * 2
def baseEnd_5822361 : Nat := 996556578997533239836985

theorem tailTrace_5822361 : CollatzResearch.WordTrace tailWord_5822361 prefixEnd_5822361 996556578997533239836985 := by
  unfold tailWord_5822361
  simp only [CollatzResearch.WordTrace]
  refine ⟨212358951659587951937266937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141572634439725301291511291 212358951659587951937266937)
  ·
    refine ⟨159269213744690963952950203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212358951659587951937266937 159269213744690963952950203)
    ·
      refine ⟨238903820617036445929425305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159269213744690963952950203 238903820617036445929425305)
      ·
        refine ⟨179177865462777334447068979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238903820617036445929425305 179177865462777334447068979)
        ·
          refine ⟨268766798194166001670603469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179177865462777334447068979 268766798194166001670603469)
          ·
            refine ⟨100787549322812250626476301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268766798194166001670603469 100787549322812250626476301)
            ·
              refine ⟨37795330996054593984928613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100787549322812250626476301 37795330996054593984928613)
              ·
                refine ⟨7086624561760236372174115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37795330996054593984928613 7086624561760236372174115)
                ·
                  refine ⟨10629936842640354558261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7086624561760236372174115 10629936842640354558261173)
                  ·
                    refine ⟨996556578997533239836985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10629936842640354558261173 996556578997533239836985)
                    ·
                      rfl

theorem cell23_5822361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_5822361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822361 prefixEnd_5822361 := by exact prefixLift 5822361
  have htrace : WordTrace (prefixWord ++ tailWord_5822361) baseStart_5822361 baseEnd_5822361 := by
    simpa [prefixWord, tailWord_5822361, baseEnd_5822361] using wordTrace_append hprefix tailTrace_5822361
  have hstable : (prefixWord ++ tailWord_5822361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822361).length < 2 ^ (prefixWord ++ tailWord_5822361).sum := by decide
  have hdescent : baseEnd_5822361 < baseStart_5822361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822368 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2]
def baseStart_5822368 : Nat := 118140960795 + 5822368 * 2 ^ 59
def prefixEnd_5822368 : Nat := 4983230072969 + 3 ^ 40 * 5822368 * 2
def baseEnd_5822368 : Nat := 2989673331357181192123423

theorem tailTrace_5822368 : CollatzResearch.WordTrace tailWord_5822368 prefixEnd_5822368 2989673331357181192123423 := by
  unfold tailWord_5822368
  simp only [CollatzResearch.WordTrace]
  refine ⟨106179603485281296066385879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141572804647041728088514505 106179603485281296066385879)
  ·
    refine ⟨159269405227921944099578819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106179603485281296066385879 159269405227921944099578819)
    ·
      refine ⟨238904107841882916149368229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159269405227921944099578819 238904107841882916149368229)
      ·
        refine ⟨44794520220353046778006543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238904107841882916149368229 44794520220353046778006543)
        ·
          refine ⟨67191780330529570167009815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44794520220353046778006543 67191780330529570167009815)
          ·
            refine ⟨100787670495794355250514723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67191780330529570167009815 100787670495794355250514723)
            ·
              refine ⟨151181505743691532875772085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100787670495794355250514723 151181505743691532875772085)
              ·
                refine ⟨14173266163471081207103633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151181505743691532875772085 14173266163471081207103633)
                ·
                  refine ⟨10629949622603310905327725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173266163471081207103633 10629949622603310905327725)
                  ·
                    refine ⟨3986231108476241589497897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10629949622603310905327725 3986231108476241589497897)
                    ·
                      refine ⟨2989673331357181192123423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986231108476241589497897 2989673331357181192123423)
                      ·
                        rfl

theorem cell23_5822368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_5822368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822368 prefixEnd_5822368 := by exact prefixLift 5822368
  have htrace : WordTrace (prefixWord ++ tailWord_5822368) baseStart_5822368 baseEnd_5822368 := by
    simpa [prefixWord, tailWord_5822368, baseEnd_5822368] using wordTrace_append hprefix tailTrace_5822368
  have hstable : (prefixWord ++ tailWord_5822368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822368).length < 2 ^ (prefixWord ++ tailWord_5822368).sum := by decide
  have hdescent : baseEnd_5822368 < baseStart_5822368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822369 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 1, 4]
def baseStart_5822369 : Nat := 118140960795 + 5822369 * 2 ^ 59
def prefixEnd_5822369 : Nat := 4983230072969 + 3 ^ 40 * 5822369 * 2
def baseEnd_5822369 : Nat := 996557948279278562736973

theorem tailTrace_5822369 : CollatzResearch.WordTrace tailWord_5822369 prefixEnd_5822369 996557948279278562736973 := by
  unfold tailWord_5822369
  simp only [CollatzResearch.WordTrace]
  refine ⟨212359243443558969303558161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141572828962372646202372107 212359243443558969303558161)
  ·
    refine ⟨159269432582669226977668621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212359243443558969303558161 159269432582669226977668621)
    ·
      refine ⟨59726037218500960116625733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159269432582669226977668621 59726037218500960116625733)
      ·
        refine ⟨11198631978468930021867325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59726037218500960116625733 11198631978468930021867325)
        ·
          refine ⟨4199486991925848758200247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11198631978468930021867325 4199486991925848758200247)
          ·
            refine ⟨6299230487888773137300371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199486991925848758200247 6299230487888773137300371)
            ·
              refine ⟨9448845731833159705950557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299230487888773137300371 9448845731833159705950557)
              ·
                refine ⟨3543317149437434889731459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9448845731833159705950557 3543317149437434889731459)
                ·
                  refine ⟨5314975724156152334597189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543317149437434889731459 5314975724156152334597189)
                  ·
                    refine ⟨996557948279278562736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314975724156152334597189 996557948279278562736973)
                    ·
                      rfl

theorem cell23_5822369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_5822369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822369 prefixEnd_5822369 := by exact prefixLift 5822369
  have htrace : WordTrace (prefixWord ++ tailWord_5822369) baseStart_5822369 baseEnd_5822369 := by
    simpa [prefixWord, tailWord_5822369, baseEnd_5822369] using wordTrace_append hprefix tailTrace_5822369
  have hstable : (prefixWord ++ tailWord_5822369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822369).length < 2 ^ (prefixWord ++ tailWord_5822369).sum := by decide
  have hdescent : baseEnd_5822369 < baseStart_5822369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822385 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5822385 : Nat := 118140960795 + 5822385 * 2 ^ 59
def prefixEnd_5822385 : Nat := 4983230072969 + 3 ^ 40 * 5822385 * 2
def baseEnd_5822385 : Nat := 2989682060528307625610845

theorem tailTrace_5822385 : CollatzResearch.WordTrace tailWord_5822385 prefixEnd_5822385 2989682060528307625610845 := by
  unfold tailWord_5822385
  simp only [CollatzResearch.WordTrace]
  refine ⟨212359827011501004036140609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141573218007667336024093739 212359827011501004036140609)
  ·
    refine ⟨159269870258625753027105457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212359827011501004036140609 159269870258625753027105457)
    ·
      refine ⟨119452402693969314770329093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159269870258625753027105457 119452402693969314770329093)
      ·
        refine ⟨22397325505119246519436705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119452402693969314770329093 22397325505119246519436705)
        ·
          refine ⟨16797994128839434889577529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22397325505119246519436705 16797994128839434889577529)
          ·
            refine ⟨12598495596629576167183147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16797994128839434889577529 12598495596629576167183147)
            ·
              refine ⟨18897743394944364250774721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598495596629576167183147 18897743394944364250774721)
              ·
                refine ⟨14173307546208273188081041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18897743394944364250774721 14173307546208273188081041)
                ·
                  refine ⟨10629980659656204891060781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173307546208273188081041 10629980659656204891060781)
                  ·
                    refine ⟨3986242747371076834147793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10629980659656204891060781 3986242747371076834147793)
                    ·
                      refine ⟨2989682060528307625610845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986242747371076834147793 2989682060528307625610845)
                      ·
                        rfl

theorem cell23_5822385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5822385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822385 prefixEnd_5822385 := by exact prefixLift 5822385
  have htrace : WordTrace (prefixWord ++ tailWord_5822385) baseStart_5822385 baseEnd_5822385 := by
    simpa [prefixWord, tailWord_5822385, baseEnd_5822385] using wordTrace_append hprefix tailTrace_5822385
  have hstable : (prefixWord ++ tailWord_5822385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822385).length < 2 ^ (prefixWord ++ tailWord_5822385).sum := by decide
  have hdescent : baseEnd_5822385 < baseStart_5822385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822392 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_5822392 : Nat := 118140960795 + 5822392 * 2 ^ 59
def prefixEnd_5822392 : Nat := 4983230072969 + 3 ^ 40 * 5822392 * 2
def baseEnd_5822392 : Nat := 2989685654892889098223313

theorem tailTrace_5822392 : CollatzResearch.WordTrace tailWord_5822392 prefixEnd_5822392 2989685654892889098223313 := by
  unfold tailWord_5822392
  simp only [CollatzResearch.WordTrace]
  refine ⟨106180041161237822115822715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141573388214983762821096953 106180041161237822115822715)
  ·
    refine ⟨159270061741856733173734073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106180041161237822115822715 159270061741856733173734073)
    ·
      refine ⟨119452546306392549880300555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159270061741856733173734073 119452546306392549880300555)
      ·
        refine ⟨179178819459588824820450833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119452546306392549880300555 179178819459588824820450833)
        ·
          refine ⟨134384114594691618615338125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179178819459588824820450833 134384114594691618615338125)
          ·
            refine ⟨50394042973009356980751797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134384114594691618615338125 50394042973009356980751797)
            ·
              refine ⟨4724441528719627216945481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50394042973009356980751797 4724441528719627216945481)
              ·
                refine ⟨3543331146539720412709111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724441528719627216945481 3543331146539720412709111)
                ·
                  refine ⟨5314996719809580619063667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543331146539720412709111 5314996719809580619063667)
                  ·
                    refine ⟨7972495079714370928595501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5314996719809580619063667 7972495079714370928595501)
                    ·
                      refine ⟨2989685654892889098223313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972495079714370928595501 2989685654892889098223313)
                      ·
                        rfl

theorem cell23_5822392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_5822392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822392 prefixEnd_5822392 := by exact prefixLift 5822392
  have htrace : WordTrace (prefixWord ++ tailWord_5822392) baseStart_5822392 baseEnd_5822392 := by
    simpa [prefixWord, tailWord_5822392, baseEnd_5822392] using wordTrace_append hprefix tailTrace_5822392
  have hstable : (prefixWord ++ tailWord_5822392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822392).length < 2 ^ (prefixWord ++ tailWord_5822392).sum := by decide
  have hdescent : baseEnd_5822392 < baseStart_5822392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822411 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_5822411 : Nat := 118140960795 + 5822411 * 2 ^ 59
def prefixEnd_5822411 : Nat := 4983230072969 + 3 ^ 40 * 5822411 * 2
def baseEnd_5822411 : Nat := 2989695411025324523885725

theorem tailTrace_5822411 : CollatzResearch.WordTrace tailWord_5822411 prefixEnd_5822411 2989695411025324523885725 := by
  unfold tailWord_5822411
  simp only [CollatzResearch.WordTrace]
  refine ⟨212360775309406810476587087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141573850206271206984391391 212360775309406810476587087)
  ·
    refine ⟨318541162964110215714880631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212360775309406810476587087 318541162964110215714880631)
    ·
      refine ⟨477811744446165323572320947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318541162964110215714880631 477811744446165323572320947)
      ·
        refine ⟨716717616669247985358481421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477811744446165323572320947 716717616669247985358481421)
        ·
          refine ⟨268769106250967994509430533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716717616669247985358481421 268769106250967994509430533)
          ·
            refine ⟨50394207422056498970518225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268769106250967994509430533 50394207422056498970518225)
            ·
              refine ⟨37795655566542374227888669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50394207422056498970518225 37795655566542374227888669)
              ·
                refine ⟨14173370837453390335458251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37795655566542374227888669 14173370837453390335458251)
                ·
                  refine ⟨21260056256180085503187377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14173370837453390335458251 21260056256180085503187377)
                  ·
                    refine ⟨15945042192135064127390533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21260056256180085503187377 15945042192135064127390533)
                    ·
                      refine ⟨2989695411025324523885725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15945042192135064127390533 2989695411025324523885725)
                      ·
                        rfl

theorem cell23_5822411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_5822411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822411 prefixEnd_5822411 := by exact prefixLift 5822411
  have htrace : WordTrace (prefixWord ++ tailWord_5822411) baseStart_5822411 baseEnd_5822411 := by
    simpa [prefixWord, tailWord_5822411, baseEnd_5822411] using wordTrace_append hprefix tailTrace_5822411
  have hstable : (prefixWord ++ tailWord_5822411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822411).length < 2 ^ (prefixWord ++ tailWord_5822411).sum := by decide
  have hdescent : baseEnd_5822411 < baseStart_5822411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822421 : List Nat := [1, 3, 2, 3, 2, 1, 2, 9]
def baseStart_5822421 : Nat := 118140960795 + 5822421 * 2 ^ 59
def prefixEnd_5822421 : Nat := 4983230072969 + 3 ^ 40 * 5822421 * 2
def baseEnd_5822421 : Nat := 110729649845624795731877

theorem tailTrace_5822421 : CollatzResearch.WordTrace tailWord_5822421 prefixEnd_5822421 110729649845624795731877 := by
  unfold tailWord_5822421
  simp only [CollatzResearch.WordTrace]
  refine ⟨212361140039370582184451117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141574093359580388122967411 212361140039370582184451117)
  ·
    refine ⟨79635427514763968319169169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212361140039370582184451117 79635427514763968319169169)
    ·
      refine ⟨59726570636072976239376877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79635427514763968319169169 59726570636072976239376877)
      ·
        refine ⟨22397463988527366089766329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59726570636072976239376877 22397463988527366089766329)
        ·
          refine ⟨16798097991395524567324747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22397463988527366089766329 16798097991395524567324747)
          ·
            refine ⟨25197146987093286850987121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16798097991395524567324747 25197146987093286850987121)
            ·
              refine ⟨18897860240319965138240341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25197146987093286850987121 18897860240319965138240341)
              ·
                refine ⟨110729649845624795731877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18897860240319965138240341 110729649845624795731877)
                ·
                  rfl

theorem cell23_5822421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 9].length) (baseStart_5822421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822421 prefixEnd_5822421 := by exact prefixLift 5822421
  have htrace : WordTrace (prefixWord ++ tailWord_5822421) baseStart_5822421 baseEnd_5822421 := by
    simpa [prefixWord, tailWord_5822421, baseEnd_5822421] using wordTrace_append hprefix tailTrace_5822421
  have hstable : (prefixWord ++ tailWord_5822421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822421).length < 2 ^ (prefixWord ++ tailWord_5822421).sum := by decide
  have hdescent : baseEnd_5822421 < baseStart_5822421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822448 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_5822448 : Nat := 118140960795 + 5822448 * 2 ^ 59
def prefixEnd_5822448 : Nat := 4983230072969 + 3 ^ 40 * 5822448 * 2
def baseEnd_5822448 : Nat := 2989714409809540879123055

theorem tailTrace_5822448 : CollatzResearch.WordTrace tailWord_5822448 prefixEnd_5822448 2989714409809540879123055 := by
  unfold tailWord_5822448
  simp only [CollatzResearch.WordTrace]
  refine ⟨106181062405136382897841999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141574749873515177197122665 106181062405136382897841999)
  ·
    refine ⟨159271593607704574346762999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106181062405136382897841999 159271593607704574346762999)
    ·
      refine ⟨238907390411556861520144499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159271593607704574346762999 238907390411556861520144499)
      ·
        refine ⟨358361085617335292280216749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238907390411556861520144499 358361085617335292280216749)
        ·
          refine ⟨134385407106500734605081281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 358361085617335292280216749 134385407106500734605081281)
          ·
            refine ⟨100789055329875550953810961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134385407106500734605081281 100789055329875550953810961)
            ·
              refine ⟨75591791497406663215358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100789055329875550953810961 75591791497406663215358221)
              ·
                refine ⟨28346921811527498705759333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75591791497406663215358221 28346921811527498705759333)
                ·
                  refine ⟨5315047839661406007329875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28346921811527498705759333 5315047839661406007329875)
                  ·
                    refine ⟨7972571759492109010994813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315047839661406007329875 7972571759492109010994813)
                    ·
                      refine ⟨2989714409809540879123055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972571759492109010994813 2989714409809540879123055)
                      ·
                        rfl

theorem cell23_5822448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_5822448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822448 prefixEnd_5822448 := by exact prefixLift 5822448
  have htrace : WordTrace (prefixWord ++ tailWord_5822448) baseStart_5822448 baseEnd_5822448 := by
    simpa [prefixWord, tailWord_5822448, baseEnd_5822448] using wordTrace_append hprefix tailTrace_5822448
  have hstable : (prefixWord ++ tailWord_5822448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822448).length < 2 ^ (prefixWord ++ tailWord_5822448).sum := by decide
  have hdescent : baseEnd_5822448 < baseStart_5822448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822449 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_5822449 : Nat := 118140960795 + 5822449 * 2 ^ 59
def prefixEnd_5822449 : Nat := 4983230072969 + 3 ^ 40 * 5822449 * 2
def baseEnd_5822449 : Nat := 2989714923290195375210551

theorem tailTrace_5822449 : CollatzResearch.WordTrace tailWord_5822449 prefixEnd_5822449 2989714923290195375210551 := by
  unfold tailWord_5822449
  simp only [CollatzResearch.WordTrace]
  refine ⟨212362161283269142966470401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141574774188846095310980267 212362161283269142966470401)
  ·
    refine ⟨159271620962451857224852801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212362161283269142966470401 159271620962451857224852801)
    ·
      refine ⟨119453715721838892918639601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159271620962451857224852801 119453715721838892918639601)
      ·
        refine ⟨89590286791379169688979701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119453715721838892918639601 89590286791379169688979701)
        ·
          refine ⟨8399089386691797158341847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89590286791379169688979701 8399089386691797158341847)
          ·
            refine ⟨12598634080037695737512771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8399089386691797158341847 12598634080037695737512771)
            ·
              refine ⟨18897951120056543606269157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598634080037695737512771 18897951120056543606269157)
              ·
                refine ⟨3543365835010601926175467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18897951120056543606269157 3543365835010601926175467)
                ·
                  refine ⟨5315048752515902889263201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543365835010601926175467 5315048752515902889263201)
                  ·
                    refine ⟨3986286564386927166947401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5315048752515902889263201 3986286564386927166947401)
                    ·
                      refine ⟨2989714923290195375210551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986286564386927166947401 2989714923290195375210551)
                      ·
                        rfl

theorem cell23_5822449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_5822449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822449 prefixEnd_5822449 := by exact prefixLift 5822449
  have htrace : WordTrace (prefixWord ++ tailWord_5822449) baseStart_5822449 baseEnd_5822449 := by
    simpa [prefixWord, tailWord_5822449, baseEnd_5822449] using wordTrace_append hprefix tailTrace_5822449
  have hstable : (prefixWord ++ tailWord_5822449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822449).length < 2 ^ (prefixWord ++ tailWord_5822449).sum := by decide
  have hdescent : baseEnd_5822449 < baseStart_5822449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822465 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_5822465 : Nat := 118140960795 + 5822465 * 2 ^ 59
def prefixEnd_5822465 : Nat := 4983230072969 + 3 ^ 40 * 5822465 * 2
def baseEnd_5822465 : Nat := 2989723138980667312610477

theorem tailTrace_5822465 : CollatzResearch.WordTrace tailWord_5822465 prefixEnd_5822465 2989723138980667312610477 := by
  unfold tailWord_5822465
  simp only [CollatzResearch.WordTrace]
  refine ⟨212362744851211177699052849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141575163234140785132701899 212362744851211177699052849)
  ·
    refine ⟨159272058638408383274289637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212362744851211177699052849 159272058638408383274289637)
    ·
      refine ⟨29863510994701571863929307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159272058638408383274289637 29863510994701571863929307)
      ·
        refine ⟨44795266492052357795893961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29863510994701571863929307 44795266492052357795893961)
        ·
          refine ⟨33596449869039268346920471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44795266492052357795893961 33596449869039268346920471)
          ·
            refine ⟨50394674803558902520380707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33596449869039268346920471 50394674803558902520380707)
            ·
              refine ⟨75592012205338353780571061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50394674803558902520380707 75592012205338353780571061)
              ·
                refine ⟨7086751144250470666928537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75592012205338353780571061 7086751144250470666928537)
                ·
                  refine ⟨5315063358187853000196403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086751144250470666928537 5315063358187853000196403)
                  ·
                    refine ⟨7972595037281779500294605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315063358187853000196403 7972595037281779500294605)
                    ·
                      refine ⟨2989723138980667312610477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972595037281779500294605 2989723138980667312610477)
                      ·
                        rfl

theorem cell23_5822465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_5822465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822465 prefixEnd_5822465 := by exact prefixLift 5822465
  have htrace : WordTrace (prefixWord ++ tailWord_5822465) baseStart_5822465 baseEnd_5822465 := by
    simpa [prefixWord, tailWord_5822465, baseEnd_5822465] using wordTrace_append hprefix tailTrace_5822465
  have hstable : (prefixWord ++ tailWord_5822465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822465).length < 2 ^ (prefixWord ++ tailWord_5822465).sum := by decide
  have hdescent : baseEnd_5822465 < baseStart_5822465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822470 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5822470 : Nat := 118140960795 + 5822470 * 2 ^ 59
def prefixEnd_5822470 : Nat := 4983230072969 + 3 ^ 40 * 5822470 * 2
def baseEnd_5822470 : Nat := 2989725706383939793047955

theorem tailTrace_5822470 : CollatzResearch.WordTrace tailWord_5822470 prefixEnd_5822470 2989725706383939793047955 := by
  unfold tailWord_5822470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636341475506033236030777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141575284810795375701989909 6636341475506033236030777)
  ·
    refine ⟨4977256106629524927023083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6636341475506033236030777 4977256106629524927023083)
    ·
      refine ⟨7465884159944287390534625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977256106629524927023083 7465884159944287390534625)
      ·
        refine ⟨5599413119958215542900969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7465884159944287390534625 5599413119958215542900969)
        ·
          refine ⟨4199559839968661657175727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5599413119958215542900969 4199559839968661657175727)
          ·
            refine ⟨6299339759952992485763591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199559839968661657175727 6299339759952992485763591)
            ·
              refine ⟨9449009639929488728645387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299339759952992485763591 9449009639929488728645387)
              ·
                refine ⟨14173514459894233092968081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449009639929488728645387 14173514459894233092968081)
                ·
                  refine ⟨10630135844920674819726061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173514459894233092968081 10630135844920674819726061)
                  ·
                    refine ⟨3986300941845253057397273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630135844920674819726061 3986300941845253057397273)
                    ·
                      refine ⟨2989725706383939793047955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986300941845253057397273 2989725706383939793047955)
                      ·
                        rfl

theorem cell23_5822470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5822470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822470 prefixEnd_5822470 := by exact prefixLift 5822470
  have htrace : WordTrace (prefixWord ++ tailWord_5822470) baseStart_5822470 baseEnd_5822470 := by
    simpa [prefixWord, tailWord_5822470, baseEnd_5822470] using wordTrace_append hprefix tailTrace_5822470
  have hstable : (prefixWord ++ tailWord_5822470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822470).length < 2 ^ (prefixWord ++ tailWord_5822470).sum := by decide
  have hdescent : baseEnd_5822470 < baseStart_5822470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822475 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 1, 3, 2]
def baseStart_5822475 : Nat := 118140960795 + 5822475 * 2 ^ 59
def prefixEnd_5822475 : Nat := 4983230072969 + 3 ^ 40 * 5822475 * 2
def baseEnd_5822475 : Nat := 2989728273787212273485431

theorem tailTrace_5822475 : CollatzResearch.WordTrace tailWord_5822475 prefixEnd_5822475 2989728273787212273485431 := by
  unfold tailWord_5822475
  simp only [CollatzResearch.WordTrace]
  refine ⟨212363109581174949406916879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141575406387449966271277919 212363109581174949406916879)
  ·
    refine ⟨318544664371762424110375319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212363109581174949406916879 318544664371762424110375319)
    ·
      refine ⟨477816996557643636165562979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318544664371762424110375319 477816996557643636165562979)
      ·
        refine ⟨716725494836465454248344469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477816996557643636165562979 716725494836465454248344469)
        ·
          refine ⟨33596507570459318167891147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 716725494836465454248344469 33596507570459318167891147)
          ·
            refine ⟨50394761355688977251836721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33596507570459318167891147 50394761355688977251836721)
            ·
              refine ⟨37796071016766732938877541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50394761355688977251836721 37796071016766732938877541)
              ·
                refine ⟨7086763315643762426039539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37796071016766732938877541 7086763315643762426039539)
                ·
                  refine ⟨10630144973465643639059309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7086763315643762426039539 10630144973465643639059309)
                  ·
                    refine ⟨3986304365049616364647241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630144973465643639059309 3986304365049616364647241)
                    ·
                      refine ⟨2989728273787212273485431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986304365049616364647241 2989728273787212273485431)
                      ·
                        rfl

theorem cell23_5822475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 3, 2].length) (baseStart_5822475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822475 prefixEnd_5822475 := by exact prefixLift 5822475
  have htrace : WordTrace (prefixWord ++ tailWord_5822475) baseStart_5822475 baseEnd_5822475 := by
    simpa [prefixWord, tailWord_5822475, baseEnd_5822475] using wordTrace_append hprefix tailTrace_5822475
  have hstable : (prefixWord ++ tailWord_5822475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822475).length < 2 ^ (prefixWord ++ tailWord_5822475).sum := by decide
  have hdescent : baseEnd_5822475 < baseStart_5822475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3]
def baseStart_5822491 : Nat := 118140960795 + 5822491 * 2 ^ 59
def prefixEnd_5822491 : Nat := 4983230072969 + 3 ^ 40 * 5822491 * 2
def baseEnd_5822491 : Nat := 2989736489477684210885357

theorem tailTrace_5822491 : CollatzResearch.WordTrace tailWord_5822491 prefixEnd_5822491 2989736489477684210885357 := by
  unfold tailWord_5822491
  simp only [CollatzResearch.WordTrace]
  refine ⟨212363693149116984139499327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141575795432744656092999551 212363693149116984139499327)
  ·
    refine ⟨318545539723675476209248991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212363693149116984139499327 318545539723675476209248991)
    ·
      refine ⟨477818309585513214313873487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318545539723675476209248991 477818309585513214313873487)
      ·
        refine ⟨716727464378269821470810231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477818309585513214313873487 716727464378269821470810231)
        ·
          refine ⟨1075091196567404732206215347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716727464378269821470810231 1075091196567404732206215347)
          ·
            refine ⟨1612636794851107098309323021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075091196567404732206215347 1612636794851107098309323021)
            ·
              refine ⟨604738798069165161865996133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1612636794851107098309323021 604738798069165161865996133)
              ·
                refine ⟨113388524637968467849874275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604738798069165161865996133 113388524637968467849874275)
                ·
                  refine ⟨170082786956952701774811413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113388524637968467849874275 170082786956952701774811413)
                  ·
                    refine ⟨7972630638607157895694285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170082786956952701774811413 7972630638607157895694285)
                    ·
                      refine ⟨2989736489477684210885357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972630638607157895694285 2989736489477684210885357)
                      ·
                        rfl

theorem cell23_5822491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].length) (baseStart_5822491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822491 prefixEnd_5822491 := by exact prefixLift 5822491
  have htrace : WordTrace (prefixWord ++ tailWord_5822491) baseStart_5822491 baseEnd_5822491 := by
    simpa [prefixWord, tailWord_5822491, baseEnd_5822491] using wordTrace_append hprefix tailTrace_5822491
  have hstable : (prefixWord ++ tailWord_5822491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822491).length < 2 ^ (prefixWord ++ tailWord_5822491).sum := by decide
  have hdescent : baseEnd_5822491 < baseStart_5822491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822492 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5822492 : Nat := 118140960795 + 5822492 * 2 ^ 59
def prefixEnd_5822492 : Nat := 4983230072969 + 3 ^ 40 * 5822492 * 2
def baseEnd_5822492 : Nat := 2989737002958338706972853

theorem tailTrace_5822492 : CollatzResearch.WordTrace tailWord_5822492 prefixEnd_5822492 2989737002958338706972853 := by
  unfold tailWord_5822492
  simp only [CollatzResearch.WordTrace]
  refine ⟨106181864811056680655142865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141575819748075574206857153 106181864811056680655142865)
  ·
    refine ⟨79636398608292510491357149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106181864811056680655142865 79636398608292510491357149)
    ·
      refine ⟨29863649478109691434258931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79636398608292510491357149 29863649478109691434258931)
      ·
        refine ⟨44795474217164537151388397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29863649478109691434258931 44795474217164537151388397)
        ·
          refine ⟨16798302831436701431770649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44795474217164537151388397 16798302831436701431770649)
          ·
            refine ⟨12598727123577526073827987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16798302831436701431770649 12598727123577526073827987)
            ·
              refine ⟨18898090685366289110741981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12598727123577526073827987 18898090685366289110741981)
              ·
                refine ⟨7086784007012358416528243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18898090685366289110741981 7086784007012358416528243)
                ·
                  refine ⟨10630176010518537624792365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7086784007012358416528243 10630176010518537624792365)
                  ·
                    refine ⟨3986316003944451609297137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630176010518537624792365 3986316003944451609297137)
                    ·
                      refine ⟨2989737002958338706972853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986316003944451609297137 2989737002958338706972853)
                      ·
                        rfl

theorem cell23_5822492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5822492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822492 prefixEnd_5822492 := by exact prefixLift 5822492
  have htrace : WordTrace (prefixWord ++ tailWord_5822492) baseStart_5822492 baseEnd_5822492 := by
    simpa [prefixWord, tailWord_5822492, baseEnd_5822492] using wordTrace_append hprefix tailTrace_5822492
  have hstable : (prefixWord ++ tailWord_5822492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822492).length < 2 ^ (prefixWord ++ tailWord_5822492).sum := by decide
  have hdescent : baseEnd_5822492 < baseStart_5822492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822516 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5822516 : Nat := 118140960795 + 5822516 * 2 ^ 59
def prefixEnd_5822516 : Nat := 4983230072969 + 3 ^ 40 * 5822516 * 2
def baseEnd_5822516 : Nat := 2989749326494046613072743

theorem tailTrace_5822516 : CollatzResearch.WordTrace tailWord_5822516 prefixEnd_5822516 2989749326494046613072743 := by
  unfold tailWord_5822516
  simp only [CollatzResearch.WordTrace]
  refine ⟨106182302487013206704579701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141576403316017608939439601 106182302487013206704579701)
  ·
    refine ⟨9954590858157488128554347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106182302487013206704579701 9954590858157488128554347)
    ·
      refine ⟨14931886287236232192831521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9954590858157488128554347 14931886287236232192831521)
      ·
        refine ⟨11198914715427174144623641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14931886287236232192831521 11198914715427174144623641)
        ·
          refine ⟨8399186036570380608467731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11198914715427174144623641 8399186036570380608467731)
          ·
            refine ⟨12598779054855570912701597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8399186036570380608467731 12598779054855570912701597)
            ·
              refine ⟨4724542145570839092263099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12598779054855570912701597 4724542145570839092263099)
              ·
                refine ⟨7086813218356258638394649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724542145570839092263099 7086813218356258638394649)
                ·
                  refine ⟨5315109913767193978795987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086813218356258638394649 5315109913767193978795987)
                  ·
                    refine ⟨7972664870650790968193981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315109913767193978795987 7972664870650790968193981)
                    ·
                      refine ⟨2989749326494046613072743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972664870650790968193981 2989749326494046613072743)
                      ·
                        rfl

theorem cell23_5822516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5822516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822516 prefixEnd_5822516 := by exact prefixLift 5822516
  have htrace : WordTrace (prefixWord ++ tailWord_5822516) baseStart_5822516 baseEnd_5822516 := by
    simpa [prefixWord, tailWord_5822516, baseEnd_5822516] using wordTrace_append hprefix tailTrace_5822516
  have hstable : (prefixWord ++ tailWord_5822516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822516).length < 2 ^ (prefixWord ++ tailWord_5822516).sum := by decide
  have hdescent : baseEnd_5822516 < baseStart_5822516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822562 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_5822562 : Nat := 118140960795 + 5822562 * 2 ^ 59
def prefixEnd_5822562 : Nat := 4983230072969 + 3 ^ 40 * 5822562 * 2
def baseEnd_5822562 : Nat := 332196994067128159233059

theorem tailTrace_5822562 : CollatzResearch.WordTrace tailWord_5822562 prefixEnd_5822562 332196994067128159233059 := by
  unfold tailWord_5822562
  simp only [CollatzResearch.WordTrace]
  refine ⟨53091570682964940816333485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141577521821239842176889293 53091570682964940816333485)
  ·
    refine ⟨19909339006111852806125057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53091570682964940816333485 19909339006111852806125057)
    ·
      refine ⟨14932004254583889604593793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19909339006111852806125057 14932004254583889604593793)
      ·
        refine ⟨11199003190937917203445345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14932004254583889604593793 11199003190937917203445345)
        ·
          refine ⟨8399252393203437902584009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11199003190937917203445345 8399252393203437902584009)
          ·
            refine ⟨6299439294902578426938007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399252393203437902584009 6299439294902578426938007)
            ·
              refine ⟨9449158942353867640407011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299439294902578426938007 9449158942353867640407011)
              ·
                refine ⟨14173738413530801460610517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449158942353867640407011 14173738413530801460610517)
                ·
                  refine ⟨332196994067128159233059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14173738413530801460610517 332196994067128159233059)
                  ·
                    rfl

theorem cell23_5822562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_5822562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822562 prefixEnd_5822562 := by exact prefixLift 5822562
  have htrace : WordTrace (prefixWord ++ tailWord_5822562) baseStart_5822562 baseEnd_5822562 := by
    simpa [prefixWord, tailWord_5822562, baseEnd_5822562] using wordTrace_append hprefix tailTrace_5822562
  have hstable : (prefixWord ++ tailWord_5822562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822562).length < 2 ^ (prefixWord ++ tailWord_5822562).sum := by decide
  have hdescent : baseEnd_5822562 < baseStart_5822562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822595 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4]
def baseStart_5822595 : Nat := 118140960795 + 5822595 * 2 ^ 59
def prefixEnd_5822595 : Nat := 4983230072969 + 3 ^ 40 * 5822595 * 2
def baseEnd_5822595 : Nat := 2989789891465751803984879

theorem tailTrace_5822595 : CollatzResearch.WordTrace tailWord_5822595 prefixEnd_5822595 2989789891465751803984879 := by
  unfold tailWord_5822595
  simp only [CollatzResearch.WordTrace]
  refine ⟨212367486340740209901285239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141578324227160139934190159 212367486340740209901285239)
  ·
    refine ⟨318551229511110314851927859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212367486340740209901285239 318551229511110314851927859)
    ·
      refine ⟨477826844266665472277891789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318551229511110314851927859 477826844266665472277891789)
      ·
        refine ⟨179185066599999552104209421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477826844266665472277891789 179185066599999552104209421)
        ·
          refine ⟨67194399974999832039078533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179185066599999552104209421 67194399974999832039078533)
          ·
            refine ⟨12598949995312468507327225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67194399974999832039078533 12598949995312468507327225)
            ·
              refine ⟨9449212496484351380495419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12598949995312468507327225 9449212496484351380495419)
              ·
                refine ⟨14173818744726527070743129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449212496484351380495419 14173818744726527070743129)
                ·
                  refine ⟨10630364058544895303057347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14173818744726527070743129 10630364058544895303057347)
                  ·
                    refine ⟨15945546087817342954586021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10630364058544895303057347 15945546087817342954586021)
                    ·
                      refine ⟨2989789891465751803984879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15945546087817342954586021 2989789891465751803984879)
                      ·
                        rfl

theorem cell23_5822595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_5822595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822595 prefixEnd_5822595 := by exact prefixLift 5822595
  have htrace : WordTrace (prefixWord ++ tailWord_5822595) baseStart_5822595 baseEnd_5822595 := by
    simpa [prefixWord, tailWord_5822595, baseEnd_5822595] using wordTrace_append hprefix tailTrace_5822595
  have hstable : (prefixWord ++ tailWord_5822595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822595).length < 2 ^ (prefixWord ++ tailWord_5822595).sum := by decide
  have hdescent : baseEnd_5822595 < baseStart_5822595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822648 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_5822648 : Nat := 118140960795 + 5822648 * 2 ^ 59
def prefixEnd_5822648 : Nat := 4983230072969 + 3 ^ 40 * 5822648 * 2
def baseEnd_5822648 : Nat := 996605701980146698874045

theorem tailTrace_5822648 : CollatzResearch.WordTrace tailWord_5822648 prefixEnd_5822648 996605701980146698874045 := by
  unfold tailWord_5822648
  simp only [CollatzResearch.WordTrace]
  refine ⟨106184709704774099976482299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141579612939698799968643065 106184709704774099976482299)
  ·
    refine ⟨159277064557161149964723449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106184709704774099976482299 159277064557161149964723449)
    ·
      refine ⟨119457798417870862473542587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159277064557161149964723449 119457798417870862473542587)
      ·
        refine ⟨179186697626806293710313881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119457798417870862473542587 179186697626806293710313881)
        ·
          refine ⟨134390023220104720282735411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179186697626806293710313881 134390023220104720282735411)
          ·
            refine ⟨201585034830157080424103117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134390023220104720282735411 201585034830157080424103117)
            ·
              refine ⟨75594388061308905159038669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201585034830157080424103117 75594388061308905159038669)
              ·
                refine ⟨28347895522990839434639501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75594388061308905159038669 28347895522990839434639501)
                ·
                  refine ⟨10630460821121564787989813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28347895522990839434639501 10630460821121564787989813)
                  ·
                    refine ⟨996605701980146698874045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10630460821121564787989813 996605701980146698874045)
                    ·
                      rfl

theorem cell23_5822648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_5822648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822648 prefixEnd_5822648 := by exact prefixLift 5822648
  have htrace : WordTrace (prefixWord ++ tailWord_5822648) baseStart_5822648 baseEnd_5822648 := by
    simpa [prefixWord, tailWord_5822648, baseEnd_5822648] using wordTrace_append hprefix tailTrace_5822648
  have hstable : (prefixWord ++ tailWord_5822648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822648).length < 2 ^ (prefixWord ++ tailWord_5822648).sum := by decide
  have hdescent : baseEnd_5822648 < baseStart_5822648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822705 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_5822705 : Nat := 118140960795 + 5822705 * 2 ^ 59
def prefixEnd_5822705 : Nat := 4983230072969 + 3 ^ 40 * 5822705 * 2
def baseEnd_5822705 : Nat := 2989846374337746373609373

theorem tailTrace_5822705 : CollatzResearch.WordTrace tailWord_5822705 prefixEnd_5822705 2989846374337746373609373 := by
  unfold tailWord_5822705
  simp only [CollatzResearch.WordTrace]
  refine ⟨212371498370341698687789569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141580998913561132458526379 212371498370341698687789569)
  ·
    refine ⟨159278623777756274015842177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212371498370341698687789569 159278623777756274015842177)
    ·
      refine ⟨119458967833317205511881633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159278623777756274015842177 119458967833317205511881633)
      ·
        refine ⟨89594225874987904133911225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119458967833317205511881633 89594225874987904133911225)
        ·
          refine ⟨67195669406240928100433419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89594225874987904133911225 67195669406240928100433419)
          ·
            refine ⟨100793504109361392150650129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67195669406240928100433419 100793504109361392150650129)
            ·
              refine ⟨75595128082021044112987597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100793504109361392150650129 75595128082021044112987597)
              ·
                refine ⟨28348173030757891542370349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75595128082021044112987597 28348173030757891542370349)
                ·
                  refine ⟨10630564886534209328388881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28348173030757891542370349 10630564886534209328388881)
                  ·
                    refine ⟨7972923664900656996291661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10630564886534209328388881 7972923664900656996291661)
                    ·
                      refine ⟨2989846374337746373609373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7972923664900656996291661 2989846374337746373609373)
                      ·
                        rfl

theorem cell23_5822705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_5822705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822705 prefixEnd_5822705 := by exact prefixLift 5822705
  have htrace : WordTrace (prefixWord ++ tailWord_5822705) baseStart_5822705 baseEnd_5822705 := by
    simpa [prefixWord, tailWord_5822705, baseEnd_5822705] using wordTrace_append hprefix tailTrace_5822705
  have hstable : (prefixWord ++ tailWord_5822705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822705).length < 2 ^ (prefixWord ++ tailWord_5822705).sum := by decide
  have hdescent : baseEnd_5822705 < baseStart_5822705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822722 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_5822722 : Nat := 118140960795 + 5822722 * 2 ^ 59
def prefixEnd_5822722 : Nat := 4983230072969 + 3 ^ 40 * 5822722 * 2
def baseEnd_5822722 : Nat := 2989855103508872807096795

theorem tailTrace_5822722 : CollatzResearch.WordTrace tailWord_5822722 prefixEnd_5822722 2989855103508872807096795 := by
  unfold tailWord_5822722
  simp only [CollatzResearch.WordTrace]
  refine ⟨53093029602820027647789605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141581412274186740394105613 53093029602820027647789605)
  ·
    refine ⟨9954943050528755183960551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53093029602820027647789605 9954943050528755183960551)
    ·
      refine ⟨14932414575793132775940827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9954943050528755183960551 14932414575793132775940827)
      ·
        refine ⟨22398621863689699163911241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14932414575793132775940827 22398621863689699163911241)
        ·
          refine ⟨16798966397767274372933431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22398621863689699163911241 16798966397767274372933431)
          ·
            refine ⟨25198449596650911559400147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16798966397767274372933431 25198449596650911559400147)
            ·
              refine ⟨37797674394976367339100221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25198449596650911559400147 37797674394976367339100221)
              ·
                refine ⟨14174127898116137752162583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37797674394976367339100221 14174127898116137752162583)
                ·
                  refine ⟨21261191847174206628243875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14174127898116137752162583 21261191847174206628243875)
                  ·
                    refine ⟨31891787770761309942365813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21261191847174206628243875 31891787770761309942365813)
                    ·
                      refine ⟨2989855103508872807096795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31891787770761309942365813 2989855103508872807096795)
                      ·
                        rfl

theorem cell23_5822722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_5822722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822722 prefixEnd_5822722 := by exact prefixLift 5822722
  have htrace : WordTrace (prefixWord ++ tailWord_5822722) baseStart_5822722 baseEnd_5822722 := by
    simpa [prefixWord, tailWord_5822722, baseEnd_5822722] using wordTrace_append hprefix tailTrace_5822722
  have hstable : (prefixWord ++ tailWord_5822722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822722).length < 2 ^ (prefixWord ++ tailWord_5822722).sum := by decide
  have hdescent : baseEnd_5822722 < baseStart_5822722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822746 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_5822746 : Nat := 118140960795 + 5822746 * 2 ^ 59
def prefixEnd_5822746 : Nat := 4983230072969 + 3 ^ 40 * 5822746 * 2
def baseEnd_5822746 : Nat := 996622475681526904398895

theorem tailTrace_5822746 : CollatzResearch.WordTrace tailWord_5822746 prefixEnd_5822746 996622475681526904398895 := by
  unfold tailWord_5822746
  simp only [CollatzResearch.WordTrace]
  refine ⟨53093248440798290672508023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141581995842128775126688061 53093248440798290672508023)
  ·
    refine ⟨79639872661197436008762035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53093248440798290672508023 79639872661197436008762035)
    ·
      refine ⟨119459808991796154013143053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79639872661197436008762035 119459808991796154013143053)
      ·
        refine ⟨44797428371923557754928645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119459808991796154013143053 44797428371923557754928645)
        ·
          refine ⟨8399517819735667079049121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44797428371923557754928645 8399517819735667079049121)
          ·
            refine ⟨6299638364801750309286841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399517819735667079049121 6299638364801750309286841)
            ·
              refine ⟨4724728773601312731965131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6299638364801750309286841 4724728773601312731965131)
              ·
                refine ⟨7087093160401969097947697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724728773601312731965131 7087093160401969097947697)
                ·
                  refine ⟨5315319870301476823460773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087093160401969097947697 5315319870301476823460773)
                  ·
                    refine ⟨996622475681526904398895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5315319870301476823460773 996622475681526904398895)
                    ·
                      rfl

theorem cell23_5822746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_5822746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822746 prefixEnd_5822746 := by exact prefixLift 5822746
  have htrace : WordTrace (prefixWord ++ tailWord_5822746) baseStart_5822746 baseEnd_5822746 := by
    simpa [prefixWord, tailWord_5822746, baseEnd_5822746] using wordTrace_append hprefix tailTrace_5822746
  have hstable : (prefixWord ++ tailWord_5822746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822746).length < 2 ^ (prefixWord ++ tailWord_5822746).sum := by decide
  have hdescent : baseEnd_5822746 < baseStart_5822746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822768 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_5822768 : Nat := 118140960795 + 5822768 * 2 ^ 59
def prefixEnd_5822768 : Nat := 4983230072969 + 3 ^ 40 * 5822768 * 2
def baseEnd_5822768 : Nat := 996626241206326542373861

theorem tailTrace_5822768 : CollatzResearch.WordTrace tailWord_5822768 prefixEnd_5822768 996626241206326542373861 := by
  unfold tailWord_5822768
  simp only [CollatzResearch.WordTrace]
  refine ⟨106186898084556730223666479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141582530779408973631555305 106186898084556730223666479)
  ·
    refine ⟨159280347126835095335499719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106186898084556730223666479 159280347126835095335499719)
    ·
      refine ⟨238920520690252643003249579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159280347126835095335499719 238920520690252643003249579)
      ·
        refine ⟨358380781035378964504874369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238920520690252643003249579 358380781035378964504874369)
        ·
          refine ⟨268785585776534223378655777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358380781035378964504874369 268785585776534223378655777)
          ·
            refine ⟨201589189332400667533991833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268785585776534223378655777 201589189332400667533991833)
            ·
              refine ⟨151191891999300500650493875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201589189332400667533991833 151191891999300500650493875)
              ·
                refine ⟨226787837998950750975740813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151191891999300500650493875 226787837998950750975740813)
                ·
                  refine ⟨85045439249606531615902805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226787837998950750975740813 85045439249606531615902805)
                  ·
                    refine ⟨996626241206326542373861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85045439249606531615902805 996626241206326542373861)
                    ·
                      rfl

theorem cell23_5822768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_5822768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822768 prefixEnd_5822768 := by exact prefixLift 5822768
  have htrace : WordTrace (prefixWord ++ tailWord_5822768) baseStart_5822768 baseEnd_5822768 := by
    simpa [prefixWord, tailWord_5822768, baseEnd_5822768] using wordTrace_append hprefix tailTrace_5822768
  have hstable : (prefixWord ++ tailWord_5822768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822768).length < 2 ^ (prefixWord ++ tailWord_5822768).sum := by decide
  have hdescent : baseEnd_5822768 < baseStart_5822768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822825 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_5822825 : Nat := 118140960795 + 5822825 * 2 ^ 59
def prefixEnd_5822825 : Nat := 4983230072969 + 3 ^ 40 * 5822825 * 2
def baseEnd_5822825 : Nat := 2989907992016285904108821

theorem tailTrace_5822825 : CollatzResearch.WordTrace tailWord_5822825 prefixEnd_5822825 2989907992016285904108821 := by
  unfold tailWord_5822825
  simp only [CollatzResearch.WordTrace]
  refine ⟨212375875129906959182157929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141583916753271306121438619 212375875129906959182157929)
  ·
    refine ⟨159281906347430219386618447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212375875129906959182157929 159281906347430219386618447)
    ·
      refine ⟨238922859521145329079927671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159281906347430219386618447 238922859521145329079927671)
      ·
        refine ⟨358384289281717993619891507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238922859521145329079927671 358384289281717993619891507)
        ·
          refine ⟨537576433922576990429837261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358384289281717993619891507 537576433922576990429837261)
          ·
            refine ⟨201591162720966371411188973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 537576433922576990429837261 201591162720966371411188973)
            ·
              refine ⟨75596686020362389279195865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201591162720966371411188973 75596686020362389279195865)
              ·
                refine ⟨56697514515271791959396899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75596686020362389279195865 56697514515271791959396899)
                ·
                  refine ⟨85046271772907687939095349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56697514515271791959396899 85046271772907687939095349)
                  ·
                    refine ⟨7973087978710095744290189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85046271772907687939095349 7973087978710095744290189)
                    ·
                      refine ⟨2989907992016285904108821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7973087978710095744290189 2989907992016285904108821)
                      ·
                        rfl

theorem cell23_5822825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_5822825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822825 prefixEnd_5822825 := by exact prefixLift 5822825
  have htrace : WordTrace (prefixWord ++ tailWord_5822825) baseStart_5822825 baseEnd_5822825 := by
    simpa [prefixWord, tailWord_5822825, baseEnd_5822825] using wordTrace_append hprefix tailTrace_5822825
  have hstable : (prefixWord ++ tailWord_5822825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822825).length < 2 ^ (prefixWord ++ tailWord_5822825).sum := by decide
  have hdescent : baseEnd_5822825 < baseStart_5822825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822832 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 5]
def baseStart_5822832 : Nat := 118140960795 + 5822832 * 2 ^ 59
def prefixEnd_5822832 : Nat := 4983230072969 + 3 ^ 40 * 5822832 * 2
def baseEnd_5822832 : Nat := 332212398486763041857921

theorem tailTrace_5822832 : CollatzResearch.WordTrace tailWord_5822832 prefixEnd_5822832 332212398486763041857921 := by
  unfold tailWord_5822832
  simp only [CollatzResearch.WordTrace]
  refine ⟨106188065220440799688831375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141584086960587732918441833 106188065220440799688831375)
  ·
    refine ⟨159282097830661199533247063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106188065220440799688831375 159282097830661199533247063)
    ·
      refine ⟨238923146745991799299870595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159282097830661199533247063 238923146745991799299870595)
      ·
        refine ⟨358384720118987698949805893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238923146745991799299870595 358384720118987698949805893)
        ·
          refine ⟨67197135022310193553088605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358384720118987698949805893 67197135022310193553088605)
          ·
            refine ⟨25198925633366322582408227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67197135022310193553088605 25198925633366322582408227)
            ·
              refine ⟨37798388450049483873612341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25198925633366322582408227 37798388450049483873612341)
              ·
                refine ⟨3543598917192139113151157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37798388450049483873612341 3543598917192139113151157)
                ·
                  refine ⟨332212398486763041857921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543598917192139113151157 332212398486763041857921)
                  ·
                    rfl

theorem cell23_5822832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 5].length) (baseStart_5822832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822832 prefixEnd_5822832 := by exact prefixLift 5822832
  have htrace : WordTrace (prefixWord ++ tailWord_5822832) baseStart_5822832 baseEnd_5822832 := by
    simpa [prefixWord, tailWord_5822832, baseEnd_5822832] using wordTrace_append hprefix tailTrace_5822832
  have hstable : (prefixWord ++ tailWord_5822832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822832).length < 2 ^ (prefixWord ++ tailWord_5822832).sum := by decide
  have hdescent : baseEnd_5822832 < baseStart_5822832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822849 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 5]
def baseStart_5822849 : Nat := 118140960795 + 5822849 * 2 ^ 59
def prefixEnd_5822849 : Nat := 4983230072969 + 3 ^ 40 * 5822849 * 2
def baseEnd_5822849 : Nat := 332213368394665978912079

theorem tailTrace_5822849 : CollatzResearch.WordTrace tailWord_5822849 prefixEnd_5822849 332213368394665978912079 := by
  unfold tailWord_5822849
  simp only [CollatzResearch.WordTrace]
  refine ⟨212376750481820011281031601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141584500321213340854021067 212376750481820011281031601)
  ·
    refine ⟨159282562861365008460773701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212376750481820011281031601 159282562861365008460773701)
    ·
      refine ⟨29865480536505939086395069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159282562861365008460773701 29865480536505939086395069)
      ·
        refine ⟨11199555201189727157398151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29865480536505939086395069 11199555201189727157398151)
        ·
          refine ⟨16799332801784590736097227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199555201189727157398151 16799332801784590736097227)
          ·
            refine ⟨25198999202676886104145841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16799332801784590736097227 25198999202676886104145841)
            ·
              refine ⟨18899249402007664578109381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25198999202676886104145841 18899249402007664578109381)
              ·
                refine ⟨3543609262876437108395509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18899249402007664578109381 3543609262876437108395509)
                ·
                  refine ⟨332213368394665978912079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543609262876437108395509 332213368394665978912079)
                  ·
                    rfl

theorem cell23_5822849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 5].length) (baseStart_5822849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822849 prefixEnd_5822849 := by exact prefixLift 5822849
  have htrace : WordTrace (prefixWord ++ tailWord_5822849) baseStart_5822849 baseEnd_5822849 := by
    simpa [prefixWord, tailWord_5822849, baseEnd_5822849] using wordTrace_append hprefix tailTrace_5822849
  have hstable : (prefixWord ++ tailWord_5822849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822849).length < 2 ^ (prefixWord ++ tailWord_5822849).sum := by decide
  have hdescent : baseEnd_5822849 < baseStart_5822849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822855 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5822855 : Nat := 118140960795 + 5822855 * 2 ^ 59
def prefixEnd_5822855 : Nat := 4983230072969 + 3 ^ 40 * 5822855 * 2
def baseEnd_5822855 : Nat := 2989923396435920786733683

theorem tailTrace_5822855 : CollatzResearch.WordTrace tailWord_5822855 prefixEnd_5822855 2989923396435920786733683 := by
  unfold tailWord_5822855
  simp only [CollatzResearch.WordTrace]
  refine ⟨212376969319798274305750019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141584646213198849537166679 212376969319798274305750019)
  ·
    refine ⟨318565453979697411458625029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212376969319798274305750019 318565453979697411458625029)
    ·
      refine ⟨59731022621193264648492193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 318565453979697411458625029 59731022621193264648492193)
      ·
        refine ⟨44798266965894948486369145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59731022621193264648492193 44798266965894948486369145)
        ·
          refine ⟨33598700224421211364776859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44798266965894948486369145 33598700224421211364776859)
          ·
            refine ⟨50398050336631817047165289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33598700224421211364776859 50398050336631817047165289)
            ·
              refine ⟨37798537752473862785373967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50398050336631817047165289 37798537752473862785373967)
              ·
                refine ⟨56697806628710794178060951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37798537752473862785373967 56697806628710794178060951)
                ·
                  refine ⟨85046709943066191267091427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56697806628710794178060951 85046709943066191267091427)
                  ·
                    refine ⟨127570064914599286900637141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85046709943066191267091427 127570064914599286900637141)
                    ·
                      refine ⟨2989923396435920786733683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127570064914599286900637141 2989923396435920786733683)
                      ·
                        rfl

theorem cell23_5822855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5822855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822855 prefixEnd_5822855 := by exact prefixLift 5822855
  have htrace : WordTrace (prefixWord ++ tailWord_5822855) baseStart_5822855 baseEnd_5822855 := by
    simpa [prefixWord, tailWord_5822855, baseEnd_5822855] using wordTrace_append hprefix tailTrace_5822855
  have hstable : (prefixWord ++ tailWord_5822855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822855).length < 2 ^ (prefixWord ++ tailWord_5822855).sum := by decide
  have hdescent : baseEnd_5822855 < baseStart_5822855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822862 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_5822862 : Nat := 118140960795 + 5822862 * 2 ^ 59
def prefixEnd_5822862 : Nat := 4983230072969 + 3 ^ 40 * 5822862 * 2
def baseEnd_5822862 : Nat := 996642330266834086448717

theorem tailTrace_5822862 : CollatzResearch.WordTrace tailWord_5822862 prefixEnd_5822862 996642330266834086448717 := by
  unfold tailWord_5822862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547153078846614312656855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141584816420515276334169893 26547153078846614312656855)
  ·
    refine ⟨39820729618269921468985283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26547153078846614312656855 39820729618269921468985283)
    ·
      refine ⟨59731094427404882203477925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39820729618269921468985283 59731094427404882203477925)
      ·
        refine ⟨11199580205138415413152111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59731094427404882203477925 11199580205138415413152111)
        ·
          refine ⟨16799370307707623119728167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199580205138415413152111 16799370307707623119728167)
          ·
            refine ⟨25199055461561434679592251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16799370307707623119728167 25199055461561434679592251)
            ·
              refine ⟨37798583192342152019388377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25199055461561434679592251 37798583192342152019388377)
              ·
                refine ⟨28348937394256614014541283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37798583192342152019388377 28348937394256614014541283)
                ·
                  refine ⟨42523406091384921021811925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28348937394256614014541283 42523406091384921021811925)
                  ·
                    refine ⟨996642330266834086448717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42523406091384921021811925 996642330266834086448717)
                    ·
                      rfl

theorem cell23_5822862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_5822862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822862 prefixEnd_5822862 := by exact prefixLift 5822862
  have htrace : WordTrace (prefixWord ++ tailWord_5822862) baseStart_5822862 baseEnd_5822862 := by
    simpa [prefixWord, tailWord_5822862, baseEnd_5822862] using wordTrace_append hprefix tailTrace_5822862
  have hstable : (prefixWord ++ tailWord_5822862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822862).length < 2 ^ (prefixWord ++ tailWord_5822862).sum := by decide
  have hdescent : baseEnd_5822862 < baseStart_5822862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822882 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5822882 : Nat := 118140960795 + 5822882 * 2 ^ 59
def prefixEnd_5822882 : Nat := 4983230072969 + 3 ^ 40 * 5822882 * 2
def baseEnd_5822882 : Nat := 2989937260413592181096059

theorem tailTrace_5822882 : CollatzResearch.WordTrace tailWord_5822882 prefixEnd_5822882 2989937260413592181096059 := by
  unfold tailWord_5822882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53094488522675114479245725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141585302727133638611321933 53094488522675114479245725)
  ·
    refine ⟨19910433196003167929717147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53094488522675114479245725 19910433196003167929717147)
    ·
      refine ⟨29865649794004751894575721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19910433196003167929717147 29865649794004751894575721)
      ·
        refine ⟨22399237345503563920931791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29865649794004751894575721 22399237345503563920931791)
        ·
          refine ⟨33598856018255345881397687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22399237345503563920931791 33598856018255345881397687)
          ·
            refine ⟨50398284027383018822096531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33598856018255345881397687 50398284027383018822096531)
            ·
              refine ⟨75597426041074528233144797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50398284027383018822096531 75597426041074528233144797)
              ·
                refine ⟨28349034765402948087429299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75597426041074528233144797 28349034765402948087429299)
                ·
                  refine ⟨42523552148104422131143949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28349034765402948087429299 42523552148104422131143949)
                  ·
                    refine ⟨15946332055539158299178981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42523552148104422131143949 15946332055539158299178981)
                    ·
                      refine ⟨2989937260413592181096059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15946332055539158299178981 2989937260413592181096059)
                      ·
                        rfl

theorem cell23_5822882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5822882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822882 prefixEnd_5822882 := by exact prefixLift 5822882
  have htrace : WordTrace (prefixWord ++ tailWord_5822882) baseStart_5822882 baseEnd_5822882 := by
    simpa [prefixWord, tailWord_5822882, baseEnd_5822882] using wordTrace_append hprefix tailTrace_5822882
  have hstable : (prefixWord ++ tailWord_5822882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822882).length < 2 ^ (prefixWord ++ tailWord_5822882).sum := by decide
  have hdescent : baseEnd_5822882 < baseStart_5822882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822900 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5822900 : Nat := 118140960795 + 5822900 * 2 ^ 59
def prefixEnd_5822900 : Nat := 4983230072969 + 3 ^ 40 * 5822900 * 2
def baseEnd_5822900 : Nat := 332216278118374790074553

theorem tailTrace_5822900 : CollatzResearch.WordTrace tailWord_5822900 prefixEnd_5822900 332216278118374790074553 := by
  unfold tailWord_5822900
  simp only [CollatzResearch.WordTrace]
  refine ⟨106189305302317623495569077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141585740403090164660758769 106189305302317623495569077)
  ·
    refine ⟨9955247372092277202709601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106189305302317623495569077 9955247372092277202709601)
    ·
      refine ⟨7466435529069207902032201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955247372092277202709601 7466435529069207902032201)
      ·
        refine ⟨5599826646801905926524151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466435529069207902032201 5599826646801905926524151)
        ·
          refine ⟨8399739970202858889786227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599826646801905926524151 8399739970202858889786227)
          ·
            refine ⟨12599609955304288334679341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8399739970202858889786227 12599609955304288334679341)
            ·
              refine ⟨4724853733239108125504753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12599609955304288334679341 4724853733239108125504753)
              ·
                refine ⟨3543640299929331094128565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724853733239108125504753 3543640299929331094128565)
                ·
                  refine ⟨332216278118374790074553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543640299929331094128565 332216278118374790074553)
                  ·
                    rfl

theorem cell23_5822900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5822900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822900 prefixEnd_5822900 := by exact prefixLift 5822900
  have htrace : WordTrace (prefixWord ++ tailWord_5822900) baseStart_5822900 baseEnd_5822900 := by
    simpa [prefixWord, tailWord_5822900, baseEnd_5822900] using wordTrace_append hprefix tailTrace_5822900
  have hstable : (prefixWord ++ tailWord_5822900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822900).length < 2 ^ (prefixWord ++ tailWord_5822900).sum := by decide
  have hdescent : baseEnd_5822900 < baseStart_5822900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822909 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_5822909 : Nat := 118140960795 + 5822909 * 2 ^ 59
def prefixEnd_5822909 : Nat := 4983230072969 + 3 ^ 40 * 5822909 * 2
def baseEnd_5822909 : Nat := 996650374797087858486145

theorem tailTrace_5822909 : CollatzResearch.WordTrace tailWord_5822909 prefixEnd_5822909 996650374797087858486145 := by
  unfold tailWord_5822909
  simp only [CollatzResearch.WordTrace]
  refine ⟨212378938861602641528215781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141585959241068427685477187 212378938861602641528215781)
  ·
    refine ⟨39821051036550495286540459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212378938861602641528215781 39821051036550495286540459)
    ·
      refine ⟨59731576554825742929810689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821051036550495286540459 59731576554825742929810689)
      ·
        refine ⟨44798682416119307197358017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59731576554825742929810689 44798682416119307197358017)
        ·
          refine ⟨33599011812089480398018513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44798682416119307197358017 33599011812089480398018513)
          ·
            refine ⟨25199258859067110298513885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33599011812089480398018513 25199258859067110298513885)
            ·
              refine ⟨9449722072150166361942707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25199258859067110298513885 9449722072150166361942707)
              ·
                refine ⟨14174583108225249542914061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449722072150166361942707 14174583108225249542914061)
                ·
                  refine ⟨5315468665584468578592773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14174583108225249542914061 5315468665584468578592773)
                  ·
                    refine ⟨996650374797087858486145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5315468665584468578592773 996650374797087858486145)
                    ·
                      rfl

theorem cell23_5822909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_5822909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822909 prefixEnd_5822909 := by exact prefixLift 5822909
  have htrace : WordTrace (prefixWord ++ tailWord_5822909) baseStart_5822909 baseEnd_5822909 := by
    simpa [prefixWord, tailWord_5822909, baseEnd_5822909] using wordTrace_append hprefix tailTrace_5822909
  have hstable : (prefixWord ++ tailWord_5822909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822909).length < 2 ^ (prefixWord ++ tailWord_5822909).sum := by decide
  have hdescent : baseEnd_5822909 < baseStart_5822909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822922 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_5822922 : Nat := 118140960795 + 5822922 * 2 ^ 59
def prefixEnd_5822922 : Nat := 4983230072969 + 3 ^ 40 * 5822922 * 2
def baseEnd_5822922 : Nat := 332217533293308002732875

theorem tailTrace_5822922 : CollatzResearch.WordTrace tailWord_5822922 prefixEnd_5822922 332217533293308002732875 := by
  unfold tailWord_5822922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53094853252638886187109755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141586275340370363165626013 53094853252638886187109755)
  ·
    refine ⟨79642279878958329280664633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53094853252638886187109755 79642279878958329280664633)
    ·
      refine ⟨59731709909218746960498475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79642279878958329280664633 59731709909218746960498475)
      ·
        refine ⟨89597564863828120440747713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59731709909218746960498475 89597564863828120440747713)
        ·
          refine ⟨67198173647871090330560785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89597564863828120440747713 67198173647871090330560785)
          ·
            refine ⟨50398630235903317747920589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67198173647871090330560785 50398630235903317747920589)
            ·
              refine ⟨18899486338463744155470221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50398630235903317747920589 18899486338463744155470221)
              ·
                refine ⟨7087307376923904058301333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18899486338463744155470221 7087307376923904058301333)
                ·
                  refine ⟨332217533293308002732875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7087307376923904058301333 332217533293308002732875)
                  ·
                    rfl

theorem cell23_5822922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_5822922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822922 prefixEnd_5822922 := by exact prefixLift 5822922
  have htrace : WordTrace (prefixWord ++ tailWord_5822922) baseStart_5822922 baseEnd_5822922 := by
    simpa [prefixWord, tailWord_5822922, baseEnd_5822922] using wordTrace_append hprefix tailTrace_5822922
  have hstable : (prefixWord ++ tailWord_5822922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822922).length < 2 ^ (prefixWord ++ tailWord_5822922).sum := by decide
  have hdescent : baseEnd_5822922 < baseStart_5822922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5822966 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5822966 : Nat := 118140960795 + 5822966 * 2 ^ 59
def prefixEnd_5822966 : Nat := 4983230072969 + 3 ^ 40 * 5822966 * 2
def baseEnd_5822966 : Nat := 2989980392788569852445673

theorem tailTrace_5822966 : CollatzResearch.WordTrace tailWord_5822966 prefixEnd_5822966 2989980392788569852445673 := by
  unfold tailWord_5822966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273813613899758766440047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141587345214930760175360501 13273813613899758766440047)
  ·
    refine ⟨19910720420849638149660071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13273813613899758766440047 19910720420849638149660071)
    ·
      refine ⟨29866080631274457224490107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19910720420849638149660071 29866080631274457224490107)
      ·
        refine ⟨44799120946911685836735161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29866080631274457224490107 44799120946911685836735161)
        ·
          refine ⟨33599340710183764377551371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44799120946911685836735161 33599340710183764377551371)
          ·
            refine ⟨50399011065275646566327057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33599340710183764377551371 50399011065275646566327057)
            ·
              refine ⟨37799258298956734924745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50399011065275646566327057 37799258298956734924745293)
              ·
                refine ⟨14174721862108775596779485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37799258298956734924745293 14174721862108775596779485)
                ·
                  refine ⟨5315520698290790848792307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14174721862108775596779485 5315520698290790848792307)
                  ·
                    refine ⟨7973281047436186273188461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315520698290790848792307 7973281047436186273188461)
                    ·
                      refine ⟨2989980392788569852445673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7973281047436186273188461 2989980392788569852445673)
                      ·
                        rfl

theorem cell23_5822966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5822966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5822966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5822966 prefixEnd_5822966 := by exact prefixLift 5822966
  have htrace : WordTrace (prefixWord ++ tailWord_5822966) baseStart_5822966 baseEnd_5822966 := by
    simpa [prefixWord, tailWord_5822966, baseEnd_5822966] using wordTrace_append hprefix tailTrace_5822966
  have hstable : (prefixWord ++ tailWord_5822966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5822966).length < 2 ^ (prefixWord ++ tailWord_5822966).sum := by decide
  have hdescent : baseEnd_5822966 < baseStart_5822966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5822966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823016 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5823016 : Nat := 118140960795 + 5823016 * 2 ^ 59
def prefixEnd_5823016 : Nat := 4983230072969 + 3 ^ 40 * 5823016 * 2
def baseEnd_5823016 : Nat := 996668688940431552273481

theorem tailTrace_5823016 : CollatzResearch.WordTrace tailWord_5823016 prefixEnd_5823016 996668688940431552273481 := by
  unfold tailWord_5823016
  simp only [CollatzResearch.WordTrace]
  refine ⟨106191420736107499401180451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141588560981476665868240601 106191420736107499401180451)
  ·
    refine ⟨159287131104161249101770677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106191420736107499401180451 159287131104161249101770677)
    ·
      refine ⟨14933168541015117103291001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159287131104161249101770677 14933168541015117103291001)
      ·
        refine ⟨11199876405761337827468251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14933168541015117103291001 11199876405761337827468251)
        ·
          refine ⟨16799814608642006741202377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199876405761337827468251 16799814608642006741202377)
          ·
            refine ⟨12599860956481505055901783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16799814608642006741202377 12599860956481505055901783)
            ·
              refine ⟨18899791434722257583852675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12599860956481505055901783 18899791434722257583852675)
              ·
                refine ⟨28349687152083386375779013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18899791434722257583852675 28349687152083386375779013)
                ·
                  refine ⟨5315566341015634945458565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28349687152083386375779013 5315566341015634945458565)
                  ·
                    refine ⟨996668688940431552273481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5315566341015634945458565 996668688940431552273481)
                    ·
                      rfl

theorem cell23_5823016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5823016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823016 prefixEnd_5823016 := by exact prefixLift 5823016
  have htrace : WordTrace (prefixWord ++ tailWord_5823016) baseStart_5823016 baseEnd_5823016 := by
    simpa [prefixWord, tailWord_5823016, baseEnd_5823016] using wordTrace_append hprefix tailTrace_5823016
  have hstable : (prefixWord ++ tailWord_5823016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823016).length < 2 ^ (prefixWord ++ tailWord_5823016).sum := by decide
  have hdescent : baseEnd_5823016 < baseStart_5823016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823036 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_5823036 : Nat := 118140960795 + 5823036 * 2 ^ 59
def prefixEnd_5823036 : Nat := 4983230072969 + 3 ^ 40 * 5823036 * 2
def baseEnd_5823036 : Nat := 2990016336434384578570351

theorem tailTrace_5823036 : CollatzResearch.WordTrace tailWord_5823036 prefixEnd_5823036 2990016336434384578570351 := by
  unfold tailWord_5823036
  simp only [CollatzResearch.WordTrace]
  refine ⟨106191785466071271109044481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141589047288095028145392641 106191785466071271109044481)
  ·
    refine ⟨79643839099553453331783361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106191785466071271109044481 79643839099553453331783361)
    ·
      refine ⟨59732879324665089998837521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79643839099553453331783361 59732879324665089998837521)
      ·
        refine ⟨44799659493498817499128141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59732879324665089998837521 44799659493498817499128141)
        ·
          refine ⟨16799872310062056562173053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44799659493498817499128141 16799872310062056562173053)
          ·
            refine ⟨6299952116273271210814895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16799872310062056562173053 6299952116273271210814895)
            ·
              refine ⟨9449928174409906816222343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299952116273271210814895 9449928174409906816222343)
              ·
                refine ⟨14174892261614860224333515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449928174409906816222343 14174892261614860224333515)
                ·
                  refine ⟨21262338392422290336500273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14174892261614860224333515 21262338392422290336500273)
                  ·
                    refine ⟨15946753794316717752375205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21262338392422290336500273 15946753794316717752375205)
                    ·
                      refine ⟨2990016336434384578570351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15946753794316717752375205 2990016336434384578570351)
                      ·
                        rfl

theorem cell23_5823036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_5823036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823036 prefixEnd_5823036 := by exact prefixLift 5823036
  have htrace : WordTrace (prefixWord ++ tailWord_5823036) baseStart_5823036 baseEnd_5823036 := by
    simpa [prefixWord, tailWord_5823036, baseEnd_5823036] using wordTrace_append hprefix tailTrace_5823036
  have hstable : (prefixWord ++ tailWord_5823036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823036).length < 2 ^ (prefixWord ++ tailWord_5823036).sum := by decide
  have hdescent : baseEnd_5823036 < baseStart_5823036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823046 : List Nat := [6, 1, 1, 1, 2, 2, 1, 9]
def baseStart_5823046 : Nat := 118140960795 + 5823046 * 2 ^ 59
def prefixEnd_5823046 : Nat := 4983230072969 + 3 ^ 40 * 5823046 * 2
def baseEnd_5823046 : Nat := 110741535971886279238715

theorem tailTrace_5823046 : CollatzResearch.WordTrace tailWord_5823046 prefixEnd_5823046 110741535971886279238715 := by
  unfold tailWord_5823046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636997989440822310186031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141589290441404209283968661 6636997989440822310186031)
  ·
    refine ⟨9955496984161233465279047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6636997989440822310186031 9955496984161233465279047)
    ·
      refine ⟨14933245476241850197918571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9955496984161233465279047 14933245476241850197918571)
      ·
        refine ⟨22399868214362775296877857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14933245476241850197918571 22399868214362775296877857)
        ·
          refine ⟨16799901160772081472658393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22399868214362775296877857 16799901160772081472658393)
          ·
            refine ⟨12599925870579061104493795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16799901160772081472658393 12599925870579061104493795)
            ·
              refine ⟨18899888805868591656740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12599925870579061104493795 18899888805868591656740693)
              ·
                refine ⟨110741535971886279238715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18899888805868591656740693 110741535971886279238715)
                ·
                  rfl

theorem cell23_5823046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_5823046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823046 prefixEnd_5823046 := by exact prefixLift 5823046
  have htrace : WordTrace (prefixWord ++ tailWord_5823046) baseStart_5823046 baseEnd_5823046 := by
    simpa [prefixWord, tailWord_5823046, baseEnd_5823046] using wordTrace_append hprefix tailTrace_5823046
  have hstable : (prefixWord ++ tailWord_5823046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823046).length < 2 ^ (prefixWord ++ tailWord_5823046).sum := by decide
  have hdescent : baseEnd_5823046 < baseStart_5823046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823052 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5823052 : Nat := 118140960795 + 5823052 * 2 ^ 59
def prefixEnd_5823052 : Nat := 4983230072969 + 3 ^ 40 * 5823052 * 2
def baseEnd_5823052 : Nat := 2990024552124856515970277

theorem tailTrace_5823052 : CollatzResearch.WordTrace tailWord_5823052 prefixEnd_5823052 2990024552124856515970277 := by
  unfold tailWord_5823052
  simp only [CollatzResearch.WordTrace]
  refine ⟨106192077250042288475335705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141589436333389717967114273 106192077250042288475335705)
  ·
    refine ⟨79644057937531716356501779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106192077250042288475335705 79644057937531716356501779)
    ·
      refine ⟨119466086906297574534752669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79644057937531716356501779 119466086906297574534752669)
      ·
        refine ⟨44799782589861590450532251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119466086906297574534752669 44799782589861590450532251)
        ·
          refine ⟨67199673884792385675798377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44799782589861590450532251 67199673884792385675798377)
          ·
            refine ⟨50399755413594289256848783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67199673884792385675798377 50399755413594289256848783)
            ·
              refine ⟨75599633120391433885273175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50399755413594289256848783 75599633120391433885273175)
              ·
                refine ⟨113399449680587150827909763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75599633120391433885273175 113399449680587150827909763)
                ·
                  refine ⟨170099174520880726241864645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113399449680587150827909763 170099174520880726241864645)
                  ·
                    refine ⟨31893595222665136170349621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170099174520880726241864645 31893595222665136170349621)
                    ·
                      refine ⟨2990024552124856515970277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31893595222665136170349621 2990024552124856515970277)
                      ·
                        rfl

theorem cell23_5823052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5823052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823052 prefixEnd_5823052 := by exact prefixLift 5823052
  have htrace : WordTrace (prefixWord ++ tailWord_5823052) baseStart_5823052 baseEnd_5823052 := by
    simpa [prefixWord, tailWord_5823052, baseEnd_5823052] using wordTrace_append hprefix tailTrace_5823052
  have hstable : (prefixWord ++ tailWord_5823052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823052).length < 2 ^ (prefixWord ++ tailWord_5823052).sum := by decide
  have hdescent : baseEnd_5823052 < baseStart_5823052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823072 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_5823072 : Nat := 118140960795 + 5823072 * 2 ^ 59
def prefixEnd_5823072 : Nat := 4983230072969 + 3 ^ 40 * 5823072 * 2
def baseEnd_5823072 : Nat := 996678273912648812573395

theorem tailTrace_5823072 : CollatzResearch.WordTrace tailWord_5823072 prefixEnd_5823072 996678273912648812573395 := by
  unfold tailWord_5823072
  simp only [CollatzResearch.WordTrace]
  refine ⟨106192441980006060183199735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141589922640008080244266313 106192441980006060183199735)
  ·
    refine ⟨159288662970009090274799603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106192441980006060183199735 159288662970009090274799603)
    ·
      refine ⟨238932994455013635412199405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159288662970009090274799603 238932994455013635412199405)
      ·
        refine ⟨89599872920630113279574777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238932994455013635412199405 89599872920630113279574777)
        ·
          refine ⟨67199904690472584959681083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89599872920630113279574777 67199904690472584959681083)
          ·
            refine ⟨100799857035708877439521625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67199904690472584959681083 100799857035708877439521625)
            ·
              refine ⟨75599892776781658079641219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100799857035708877439521625 75599892776781658079641219)
              ·
                refine ⟨113399839165172487119461829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75599892776781658079641219 113399839165172487119461829)
                ·
                  refine ⟨21262469843469841334899093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113399839165172487119461829 21262469843469841334899093)
                  ·
                    refine ⟨996678273912648812573395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21262469843469841334899093 996678273912648812573395)
                    ·
                      rfl

theorem cell23_5823072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_5823072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823072 prefixEnd_5823072 := by exact prefixLift 5823072
  have htrace : WordTrace (prefixWord ++ tailWord_5823072) baseStart_5823072 baseEnd_5823072 := by
    simpa [prefixWord, tailWord_5823072, baseEnd_5823072] using wordTrace_append hprefix tailTrace_5823072
  have hstable : (prefixWord ++ tailWord_5823072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823072).length < 2 ^ (prefixWord ++ tailWord_5823072).sum := by decide
  have hdescent : baseEnd_5823072 < baseStart_5823072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823074 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5823074 : Nat := 118140960795 + 5823074 * 2 ^ 59
def prefixEnd_5823074 : Nat := 4983230072969 + 3 ^ 40 * 5823074 * 2
def baseEnd_5823074 : Nat := 2990035848699255429895177

theorem tailTrace_5823074 : CollatzResearch.WordTrace tailWord_5823074 prefixEnd_5823074 2990035848699255429895177 := by
  unfold tailWord_5823074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53096239226501218676993069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141589971270669916471981517 53096239226501218676993069)
  ·
    refine ⟨19911089709937957003872401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53096239226501218676993069 19911089709937957003872401)
    ·
      refine ⟨14933317282453467752904301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19911089709937957003872401 14933317282453467752904301)
      ·
        refine ⟨5599993980920050407339113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14933317282453467752904301 5599993980920050407339113)
        ·
          refine ⟨4199995485690037805504335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5599993980920050407339113 4199995485690037805504335)
          ·
            refine ⟨6299993228535056708256503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199995485690037805504335 6299993228535056708256503)
            ·
              refine ⟨9449989842802585062384755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299993228535056708256503 9449989842802585062384755)
              ·
                refine ⟨14174984764203877593577133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9449989842802585062384755 14174984764203877593577133)
                ·
                  refine ⟨5315619286576454097591425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14174984764203877593577133 5315619286576454097591425)
                  ·
                    refine ⟨3986714464932340573193569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5315619286576454097591425 3986714464932340573193569)
                    ·
                      refine ⟨2990035848699255429895177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986714464932340573193569 2990035848699255429895177)
                      ·
                        rfl

theorem cell23_5823074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5823074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823074 prefixEnd_5823074 := by exact prefixLift 5823074
  have htrace : WordTrace (prefixWord ++ tailWord_5823074) baseStart_5823074 baseEnd_5823074 := by
    simpa [prefixWord, tailWord_5823074, baseEnd_5823074] using wordTrace_append hprefix tailTrace_5823074
  have hstable : (prefixWord ++ tailWord_5823074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823074).length < 2 ^ (prefixWord ++ tailWord_5823074).sum := by decide
  have hdescent : baseEnd_5823074 < baseStart_5823074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823129 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_5823129 : Nat := 118140960795 + 5823129 * 2 ^ 59
def prefixEnd_5823129 : Nat := 4983230072969 + 3 ^ 40 * 5823129 * 2
def baseEnd_5823129 : Nat := 2990064090135252714707423

theorem tailTrace_5823129 : CollatzResearch.WordTrace tailWord_5823129 prefixEnd_5823129 2990064090135252714707423 := by
  unfold tailWord_5823129
  simp only [CollatzResearch.WordTrace]
  refine ⟨212386962920805619101224441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141591308613870412734149627 212386962920805619101224441)
  ·
    refine ⟨159290222190604214325918331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212386962920805619101224441 159290222190604214325918331)
    ·
      refine ⟨238935333285906321488877497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159290222190604214325918331 238935333285906321488877497)
      ·
        refine ⟨179201499964429741116658123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238935333285906321488877497 179201499964429741116658123)
        ·
          refine ⟨268802249946644611674987185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179201499964429741116658123 268802249946644611674987185)
          ·
            refine ⟨201601687459983458756240389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268802249946644611674987185 201601687459983458756240389)
            ·
              refine ⟨37800316398746898516795073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201601687459983458756240389 37800316398746898516795073)
              ·
                refine ⟨28350237299060173887596305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37800316398746898516795073 28350237299060173887596305)
                ·
                  refine ⟨21262677974295130415697229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28350237299060173887596305 21262677974295130415697229)
                  ·
                    refine ⟨7973504240360673905886461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21262677974295130415697229 7973504240360673905886461)
                    ·
                      refine ⟨2990064090135252714707423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7973504240360673905886461 2990064090135252714707423)
                      ·
                        rfl

theorem cell23_5823129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_5823129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823129 prefixEnd_5823129 := by exact prefixLift 5823129
  have htrace : WordTrace (prefixWord ++ tailWord_5823129) baseStart_5823129 baseEnd_5823129 := by
    simpa [prefixWord, tailWord_5823129, baseEnd_5823129] using wordTrace_append hprefix tailTrace_5823129
  have hstable : (prefixWord ++ tailWord_5823129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823129).length < 2 ^ (prefixWord ++ tailWord_5823129).sum := by decide
  have hdescent : baseEnd_5823129 < baseStart_5823129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823143 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5823143 : Nat := 118140960795 + 5823143 * 2 ^ 59
def prefixEnd_5823143 : Nat := 4983230072969 + 3 ^ 40 * 5823143 * 2
def baseEnd_5823143 : Nat := 2990071278864415659932359

theorem tailTrace_5823143 : CollatzResearch.WordTrace tailWord_5823143 prefixEnd_5823143 2990071278864415659932359 := by
  unfold tailWord_5823143
  simp only [CollatzResearch.WordTrace]
  refine ⟨212387473542754899492234083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141591649028503266328156055 212387473542754899492234083)
  ·
    refine ⟨318581210314132349238351125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212387473542754899492234083 318581210314132349238351125)
    ·
      refine ⟨14933494233474953870547709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 318581210314132349238351125 14933494233474953870547709)
      ·
        refine ⟨5600060337553107701455391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14933494233474953870547709 5600060337553107701455391)
        ·
          refine ⟨8400090506329661552183087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600060337553107701455391 8400090506329661552183087)
          ·
            refine ⟨12600135759494492328274631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400090506329661552183087 12600135759494492328274631)
            ·
              refine ⟨18900203639241738492411947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12600135759494492328274631 18900203639241738492411947)
              ·
                refine ⟨28350305458862607738617921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18900203639241738492411947 28350305458862607738617921)
                ·
                  refine ⟨21262729094146955803963441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28350305458862607738617921 21262729094146955803963441)
                  ·
                    refine ⟨15947046820610216852972581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21262729094146955803963441 15947046820610216852972581)
                    ·
                      refine ⟨2990071278864415659932359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15947046820610216852972581 2990071278864415659932359)
                      ·
                        rfl

theorem cell23_5823143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5823143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823143 prefixEnd_5823143 := by exact prefixLift 5823143
  have htrace : WordTrace (prefixWord ++ tailWord_5823143) baseStart_5823143 baseEnd_5823143 := by
    simpa [prefixWord, tailWord_5823143, baseEnd_5823143] using wordTrace_append hprefix tailTrace_5823143
  have hstable : (prefixWord ++ tailWord_5823143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823143).length < 2 ^ (prefixWord ++ tailWord_5823143).sum := by decide
  have hdescent : baseEnd_5823143 < baseStart_5823143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823181 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5823181 : Nat := 118140960795 + 5823181 * 2 ^ 59
def prefixEnd_5823181 : Nat := 4983230072969 + 3 ^ 40 * 5823181 * 2
def baseEnd_5823181 : Nat := 2990090791129286511257185

theorem tailTrace_5823181 : CollatzResearch.WordTrace tailWord_5823181 prefixEnd_5823181 2990090791129286511257185 := by
  unfold tailWord_5823181
  simp only [CollatzResearch.WordTrace]
  refine ⟨212388859516617231982117397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141592573011078154654744931 212388859516617231982117397)
  ·
    refine ⟨9955727789841432749161753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 212388859516617231982117397 9955727789841432749161753)
    ·
      refine ⟨7466795842381074561871315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955727789841432749161753 7466795842381074561871315)
      ·
        refine ⟨11200193763571611842806973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7466795842381074561871315 11200193763571611842806973)
        ·
          refine ⟨4200072661339354441052615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11200193763571611842806973 4200072661339354441052615)
          ·
            refine ⟨6300108992009031661578923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200072661339354441052615 6300108992009031661578923)
            ·
              refine ⟨9450163488013547492368385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300108992009031661578923 9450163488013547492368385)
              ·
                refine ⟨7087622616010160619276289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9450163488013547492368385 7087622616010160619276289)
                ·
                  refine ⟨5315716962007620464457217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087622616010160619276289 5315716962007620464457217)
                  ·
                    refine ⟨3986787721505715348342913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5315716962007620464457217 3986787721505715348342913)
                    ·
                      refine ⟨2990090791129286511257185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986787721505715348342913 2990090791129286511257185)
                      ·
                        rfl

theorem cell23_5823181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5823181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823181 prefixEnd_5823181 := by exact prefixLift 5823181
  have htrace : WordTrace (prefixWord ++ tailWord_5823181) baseStart_5823181 baseEnd_5823181 := by
    simpa [prefixWord, tailWord_5823181, baseEnd_5823181] using wordTrace_append hprefix tailTrace_5823181
  have hstable : (prefixWord ++ tailWord_5823181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823181).length < 2 ^ (prefixWord ++ tailWord_5823181).sum := by decide
  have hdescent : baseEnd_5823181 < baseStart_5823181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823203 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5823203 : Nat := 118140960795 + 5823203 * 2 ^ 59
def prefixEnd_5823203 : Nat := 4983230072969 + 3 ^ 40 * 5823203 * 2
def baseEnd_5823203 : Nat := 2990102087703685425182083

theorem tailTrace_5823203 : CollatzResearch.WordTrace tailWord_5823203 prefixEnd_5823203 2990102087703685425182083 := by
  unfold tailWord_5823203
  simp only [CollatzResearch.WordTrace]
  refine ⟨212389661922537529739418263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141593107948358353159612175 212389661922537529739418263)
  ·
    refine ⟨318584492883806294609127395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212389661922537529739418263 318584492883806294609127395)
    ·
      refine ⟨477876739325709441913691093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318584492883806294609127395 477876739325709441913691093)
      ·
        refine ⟨11200236077946315044852135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 477876739325709441913691093 11200236077946315044852135)
        ·
          refine ⟨16800354116919472567278203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11200236077946315044852135 16800354116919472567278203)
          ·
            refine ⟨25200531175379208850917305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16800354116919472567278203 25200531175379208850917305)
            ·
              refine ⟨18900398381534406638187979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25200531175379208850917305 18900398381534406638187979)
              ·
                refine ⟨28350597572301609957281969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18900398381534406638187979 28350597572301609957281969)
                ·
                  refine ⟨21262948179226207467961477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28350597572301609957281969 21262948179226207467961477)
                  ·
                    refine ⟨3986802783604913900242777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21262948179226207467961477 3986802783604913900242777)
                    ·
                      refine ⟨2990102087703685425182083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3986802783604913900242777 2990102087703685425182083)
                      ·
                        rfl

theorem cell23_5823203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5823203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823203 prefixEnd_5823203 := by exact prefixLift 5823203
  have htrace : WordTrace (prefixWord ++ tailWord_5823203) baseStart_5823203 baseEnd_5823203 := by
    simpa [prefixWord, tailWord_5823203, baseEnd_5823203] using wordTrace_append hprefix tailTrace_5823203
  have hstable : (prefixWord ++ tailWord_5823203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823203).length < 2 ^ (prefixWord ++ tailWord_5823203).sum := by decide
  have hdescent : baseEnd_5823203 < baseStart_5823203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823209 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 6]
def baseStart_5823209 : Nat := 118140960795 + 5823209 * 2 ^ 59
def prefixEnd_5823209 : Nat := 4983230072969 + 3 ^ 40 * 5823209 * 2
def baseEnd_5823209 : Nat := 332233907620845822411895

theorem tailTrace_5823209 : CollatzResearch.WordTrace tailWord_5823209 prefixEnd_5823209 332233907620845822411895 := by
  unfold tailWord_5823209
  simp only [CollatzResearch.WordTrace]
  refine ⟨212389880760515792764136681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141593253840343861842757787 212389880760515792764136681)
  ·
    refine ⟨159292410570386844573102511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212389880760515792764136681 159292410570386844573102511)
    ·
      refine ⟨238938615855580266859653767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159292410570386844573102511 238938615855580266859653767)
      ·
        refine ⟨358407923783370400289480651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238938615855580266859653767 358407923783370400289480651)
        ·
          refine ⟨537611885675055600434220977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358407923783370400289480651 537611885675055600434220977)
          ·
            refine ⟨403208914256291700325665733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537611885675055600434220977 403208914256291700325665733)
            ·
              refine ⟨75601671423054693811062325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 403208914256291700325665733 75601671423054693811062325)
              ·
                refine ⟨7087656695911377544787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75601671423054693811062325 7087656695911377544787093)
                ·
                  refine ⟨332233907620845822411895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7087656695911377544787093 332233907620845822411895)
                  ·
                    rfl

theorem cell23_5823209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_5823209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823209 prefixEnd_5823209 := by exact prefixLift 5823209
  have htrace : WordTrace (prefixWord ++ tailWord_5823209) baseStart_5823209 baseEnd_5823209 := by
    simpa [prefixWord, tailWord_5823209, baseEnd_5823209] using wordTrace_append hprefix tailTrace_5823209
  have hstable : (prefixWord ++ tailWord_5823209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823209).length < 2 ^ (prefixWord ++ tailWord_5823209).sum := by decide
  have hdescent : baseEnd_5823209 < baseStart_5823209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823219 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3]
def baseStart_5823219 : Nat := 118140960795 + 5823219 * 2 ^ 59
def prefixEnd_5823219 : Nat := 4983230072969 + 3 ^ 40 * 5823219 * 2
def baseEnd_5823219 : Nat := 2990110303394157362582009

theorem tailTrace_5823219 : CollatzResearch.WordTrace tailWord_5823219 prefixEnd_5823219 2990110303394157362582009 := by
  unfold tailWord_5823219
  simp only [CollatzResearch.WordTrace]
  refine ⟨212390245490479564472000711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141593496993653042981333807 212390245490479564472000711)
  ·
    refine ⟨318585368235719346708001067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212390245490479564472000711 318585368235719346708001067)
    ·
      refine ⟨477878052353579020062001601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318585368235719346708001067 477878052353579020062001601)
      ·
        refine ⟨358408539265184265046501201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477878052353579020062001601 358408539265184265046501201)
        ·
          refine ⟨268806404448888198784875901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358408539265184265046501201 268806404448888198784875901)
          ·
            refine ⟨100802401668333074544328463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268806404448888198784875901 100802401668333074544328463)
            ·
              refine ⟨151203602502499611816492695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100802401668333074544328463 151203602502499611816492695)
              ·
                refine ⟨226805403753749417724739043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151203602502499611816492695 226805403753749417724739043)
                ·
                  refine ⟨340208105630624126587108565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226805403753749417724739043 340208105630624126587108565)
                  ·
                    refine ⟨7973627475717752966885357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 340208105630624126587108565 7973627475717752966885357)
                    ·
                      refine ⟨2990110303394157362582009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7973627475717752966885357 2990110303394157362582009)
                      ·
                        rfl

theorem cell23_5823219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_5823219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823219 prefixEnd_5823219 := by exact prefixLift 5823219
  have htrace : WordTrace (prefixWord ++ tailWord_5823219) baseStart_5823219 baseEnd_5823219 := by
    simpa [prefixWord, tailWord_5823219, baseEnd_5823219] using wordTrace_append hprefix tailTrace_5823219
  have hstable : (prefixWord ++ tailWord_5823219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823219).length < 2 ^ (prefixWord ++ tailWord_5823219).sum := by decide
  have hdescent : baseEnd_5823219 < baseStart_5823219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823276 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_5823276 : Nat := 118140960795 + 5823276 * 2 ^ 59
def prefixEnd_5823276 : Nat := 4983230072969 + 3 ^ 40 * 5823276 * 2
def baseEnd_5823276 : Nat := 2990139571791463639569247

theorem tailTrace_5823276 : CollatzResearch.WordTrace tailWord_5823276 prefixEnd_5823276 2990139571791463639569247 := by
  unfold tailWord_5823276
  simp only [CollatzResearch.WordTrace]
  refine ⟨106196162225636531603412841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141594882967515375471217121 106196162225636531603412841)
  ·
    refine ⟨79647121669227398702559631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106196162225636531603412841 79647121669227398702559631)
    ·
      refine ⟨119470682503841098053839447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79647121669227398702559631 119470682503841098053839447)
      ·
        refine ⟨179206023755761647080759171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119470682503841098053839447 179206023755761647080759171)
        ·
          refine ⟨268809035633642470621138757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179206023755761647080759171 268809035633642470621138757)
          ·
            refine ⟨50401694181307963241463517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268809035633642470621138757 50401694181307963241463517)
            ·
              refine ⟨18900635317990486215548819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50401694181307963241463517 18900635317990486215548819)
              ·
                refine ⟨28350952976985729323323229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18900635317990486215548819 28350952976985729323323229)
                ·
                  refine ⟨10631607366369648496246211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28350952976985729323323229 10631607366369648496246211)
                  ·
                    refine ⟨15947411049554472744369317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10631607366369648496246211 15947411049554472744369317)
                    ·
                      refine ⟨2990139571791463639569247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15947411049554472744369317 2990139571791463639569247)
                      ·
                        rfl

theorem cell23_5823276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_5823276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823276 prefixEnd_5823276 := by exact prefixLift 5823276
  have htrace : WordTrace (prefixWord ++ tailWord_5823276) baseStart_5823276 baseEnd_5823276 := by
    simpa [prefixWord, tailWord_5823276, baseEnd_5823276] using wordTrace_append hprefix tailTrace_5823276
  have hstable : (prefixWord ++ tailWord_5823276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823276).length < 2 ^ (prefixWord ++ tailWord_5823276).sum := by decide
  have hdescent : baseEnd_5823276 < baseStart_5823276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823290 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_5823290 : Nat := 118140960795 + 5823290 * 2 ^ 59
def prefixEnd_5823290 : Nat := 4983230072969 + 3 ^ 40 * 5823290 * 2
def baseEnd_5823290 : Nat := 996715586840208861598061

theorem tailTrace_5823290 : CollatzResearch.WordTrace tailWord_5823290 prefixEnd_5823290 996715586840208861598061 := by
  unfold tailWord_5823290
  simp only [CollatzResearch.WordTrace]
  refine ⟨53098208768305585899458831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141595223382148229065223549 53098208768305585899458831)
  ·
    refine ⟨79647313152458378849188247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53098208768305585899458831 79647313152458378849188247)
    ·
      refine ⟨119470969728687568273782371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79647313152458378849188247 119470969728687568273782371)
      ·
        refine ⟨179206454593031352410673557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119470969728687568273782371 179206454593031352410673557)
        ·
          refine ⟨8400302559048344644250323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179206454593031352410673557 8400302559048344644250323)
          ·
            refine ⟨12600453838572516966375485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400302559048344644250323 12600453838572516966375485)
            ·
              refine ⟨4725170189464693862390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12600453838572516966375485 4725170189464693862390807)
              ·
                refine ⟨7087755284197040793586211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725170189464693862390807 7087755284197040793586211)
                ·
                  refine ⟨10631632926295561190379317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7087755284197040793586211 10631632926295561190379317)
                  ·
                    refine ⟨996715586840208861598061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10631632926295561190379317 996715586840208861598061)
                    ·
                      rfl

theorem cell23_5823290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_5823290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823290 prefixEnd_5823290 := by exact prefixLift 5823290
  have htrace : WordTrace (prefixWord ++ tailWord_5823290) baseStart_5823290 baseEnd_5823290 := by
    simpa [prefixWord, tailWord_5823290, baseEnd_5823290] using wordTrace_append hprefix tailTrace_5823290
  have hstable : (prefixWord ++ tailWord_5823290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823290).length < 2 ^ (prefixWord ++ tailWord_5823290).sum := by decide
  have hdescent : baseEnd_5823290 < baseStart_5823290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823428 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5823428 : Nat := 118140960795 + 5823428 * 2 ^ 59
def prefixEnd_5823428 : Nat := 4983230072969 + 3 ^ 40 * 5823428 * 2
def baseEnd_5823428 : Nat := 2990217620850947044868549

theorem tailTrace_5823428 : CollatzResearch.WordTrace tailWord_5823428 prefixEnd_5823428 2990217620850947044868549 := by
  unfold tailWord_5823428
  simp only [CollatzResearch.WordTrace]
  refine ⟨106198934173361196583179469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141598578897814928777572625 106198934173361196583179469)
  ·
    refine ⟨39824600315010448718692301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106198934173361196583179469 39824600315010448718692301)
    ·
      refine ⟨14934225118128918269509613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39824600315010448718692301 14934225118128918269509613)
      ·
        refine ⟨5600334419298344351066105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14934225118128918269509613 5600334419298344351066105)
        ·
          refine ⟨4200250814473758263299579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600334419298344351066105 4200250814473758263299579)
          ·
            refine ⟨6300376221710637394949369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200250814473758263299579 6300376221710637394949369)
            ·
              refine ⟨4725282166282978046212027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6300376221710637394949369 4725282166282978046212027)
              ·
                refine ⟨7087923249424467069318041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725282166282978046212027 7087923249424467069318041)
                ·
                  refine ⟨5315942437068350301988531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7087923249424467069318041 5315942437068350301988531)
                  ·
                    refine ⟨7973913655602525452982797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5315942437068350301988531 7973913655602525452982797)
                    ·
                      refine ⟨2990217620850947044868549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7973913655602525452982797 2990217620850947044868549)
                      ·
                        rfl

theorem cell23_5823428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5823428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823428 prefixEnd_5823428 := by exact prefixLift 5823428
  have htrace : WordTrace (prefixWord ++ tailWord_5823428) baseStart_5823428 baseEnd_5823428 := by
    simpa [prefixWord, tailWord_5823428, baseEnd_5823428] using wordTrace_append hprefix tailTrace_5823428
  have hstable : (prefixWord ++ tailWord_5823428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823428).length < 2 ^ (prefixWord ++ tailWord_5823428).sum := by decide
  have hdescent : baseEnd_5823428 < baseStart_5823428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823463 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5823463 : Nat := 118140960795 + 5823463 * 2 ^ 59
def prefixEnd_5823463 : Nat := 4983230072969 + 3 ^ 40 * 5823463 * 2
def baseEnd_5823463 : Nat := 2990235592673854407930887

theorem tailTrace_5823463 : CollatzResearch.WordTrace tailWord_5823463 prefixEnd_5823463 2990235592673854407930887 := by
  unfold tailWord_5823463
  simp only [CollatzResearch.WordTrace]
  refine ⟨212399144901595594143883043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141599429934397062762588695 212399144901595594143883043)
  ·
    refine ⟨318598717352393391215824565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212399144901595594143883043 318598717352393391215824565)
    ·
      refine ⟨29868629751786880426483553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 318598717352393391215824565 29868629751786880426483553)
      ·
        refine ⟨22401472313840160319862665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29868629751786880426483553 22401472313840160319862665)
        ·
          refine ⟨16801104235380120239896999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22401472313840160319862665 16801104235380120239896999)
          ·
            refine ⟨25201656353070180359845499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16801104235380120239896999 25201656353070180359845499)
            ·
              refine ⟨37802484529605270539768249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25201656353070180359845499 37802484529605270539768249)
              ·
                refine ⟨28351863397203952904826187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37802484529605270539768249 28351863397203952904826187)
                ·
                  refine ⟨42527795095805929357239281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28351863397203952904826187 42527795095805929357239281)
                  ·
                    refine ⟨31895846321854447017929461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42527795095805929357239281 31895846321854447017929461)
                    ·
                      refine ⟨2990235592673854407930887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31895846321854447017929461 2990235592673854407930887)
                      ·
                        rfl

theorem cell23_5823463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5823463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823463 prefixEnd_5823463 := by exact prefixLift 5823463
  have htrace : WordTrace (prefixWord ++ tailWord_5823463) baseStart_5823463 baseEnd_5823463 := by
    simpa [prefixWord, tailWord_5823463, baseEnd_5823463] using wordTrace_append hprefix tailTrace_5823463
  have hstable : (prefixWord ++ tailWord_5823463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823463).length < 2 ^ (prefixWord ++ tailWord_5823463).sum := by decide
  have hdescent : baseEnd_5823463 < baseStart_5823463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823483 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 3, 4]
def baseStart_5823483 : Nat := 118140960795 + 5823483 * 2 ^ 59
def prefixEnd_5823483 : Nat := 4983230072969 + 3 ^ 40 * 5823483 * 2
def baseEnd_5823483 : Nat := 996748620762314776560265

theorem tailTrace_5823483 : CollatzResearch.WordTrace tailWord_5823483 prefixEnd_5823483 996748620762314776560265 := by
  unfold tailWord_5823483
  simp only [CollatzResearch.WordTrace]
  refine ⟨212399874361523137559611103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141599916241015425039740735 212399874361523137559611103)
  ·
    refine ⟨318599811542284706339416655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212399874361523137559611103 318599811542284706339416655)
    ·
      refine ⟨477899717313427059509124983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318599811542284706339416655 477899717313427059509124983)
      ·
        refine ⟨716849575970140589263687475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477899717313427059509124983 716849575970140589263687475)
        ·
          refine ⟨1075274363955210883895531213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716849575970140589263687475 1075274363955210883895531213)
          ·
            refine ⟨403227886483204081460824205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1075274363955210883895531213 403227886483204081460824205)
            ·
              refine ⟨151210457431201530547809077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403227886483204081460824205 151210457431201530547809077)
              ·
                refine ⟨14175980384175143488857101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151210457431201530547809077 14175980384175143488857101)
                ·
                  refine ⟨5315992644065678808321413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14175980384175143488857101 5315992644065678808321413)
                  ·
                    refine ⟨996748620762314776560265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5315992644065678808321413 996748620762314776560265)
                    ·
                      rfl

theorem cell23_5823483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 4].length) (baseStart_5823483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823483 prefixEnd_5823483 := by exact prefixLift 5823483
  have htrace : WordTrace (prefixWord ++ tailWord_5823483) baseStart_5823483 baseEnd_5823483 := by
    simpa [prefixWord, tailWord_5823483, baseEnd_5823483] using wordTrace_append hprefix tailTrace_5823483
  have hstable : (prefixWord ++ tailWord_5823483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823483).length < 2 ^ (prefixWord ++ tailWord_5823483).sum := by decide
  have hdescent : baseEnd_5823483 < baseStart_5823483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823493 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_5823493 : Nat := 118140960795 + 5823493 * 2 ^ 59
def prefixEnd_5823493 : Nat := 4983230072969 + 3 ^ 40 * 5823493 * 2
def baseEnd_5823493 : Nat := 2990250997093489290555749

theorem tailTrace_5823493 : CollatzResearch.WordTrace tailWord_5823493 prefixEnd_5823493 2990250997093489290555749 := by
  unfold tailWord_5823493
  simp only [CollatzResearch.WordTrace]
  refine ⟨212400239091486909267475133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141600159394324606178316755 212400239091486909267475133)
  ·
    refine ⟨79650089659307590975303175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212400239091486909267475133 79650089659307590975303175)
    ·
      refine ⟨119475134488961386462954763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79650089659307590975303175 119475134488961386462954763)
      ·
        refine ⟨179212701733442079694432145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119475134488961386462954763 179212701733442079694432145)
        ·
          refine ⟨134409526300081559770824109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179212701733442079694432145 134409526300081559770824109)
          ·
            refine ⟨50403572362530584914059041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134409526300081559770824109 50403572362530584914059041)
            ·
              refine ⟨37802679271897938685544281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50403572362530584914059041 37802679271897938685544281)
              ·
                refine ⟨28352009453923454014158211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37802679271897938685544281 28352009453923454014158211)
                ·
                  refine ⟨42528014180885181021237317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28352009453923454014158211 42528014180885181021237317)
                  ·
                    refine ⟨7974002658915971441481997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42528014180885181021237317 7974002658915971441481997)
                    ·
                      refine ⟨2990250997093489290555749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974002658915971441481997 2990250997093489290555749)
                      ·
                        rfl

theorem cell23_5823493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_5823493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823493 prefixEnd_5823493 := by exact prefixLift 5823493
  have htrace : WordTrace (prefixWord ++ tailWord_5823493) baseStart_5823493 baseEnd_5823493 := by
    simpa [prefixWord, tailWord_5823493, baseEnd_5823493] using wordTrace_append hprefix tailTrace_5823493
  have hstable : (prefixWord ++ tailWord_5823493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823493).length < 2 ^ (prefixWord ++ tailWord_5823493).sum := by decide
  have hdescent : baseEnd_5823493 < baseStart_5823493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823500 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_5823500 : Nat := 118140960795 + 5823500 * 2 ^ 59
def prefixEnd_5823500 : Nat := 4983230072969 + 3 ^ 40 * 5823500 * 2
def baseEnd_5823500 : Nat := 996751530486023587722739

theorem tailTrace_5823500 : CollatzResearch.WordTrace tailWord_5823500 prefixEnd_5823500 996751530486023587722739 := by
  unfold tailWord_5823500
  simp only [CollatzResearch.WordTrace]
  refine ⟨106200247201230774731489977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141600329601641032975319969 106200247201230774731489977)
  ·
    refine ⟨79650185400923081048617483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106200247201230774731489977 79650185400923081048617483)
    ·
      refine ⟨119475278101384621572926225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79650185400923081048617483 119475278101384621572926225)
      ·
        refine ⟨89606458576038466179694669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119475278101384621572926225 89606458576038466179694669)
        ·
          refine ⟨33602421966014424817385501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89606458576038466179694669 33602421966014424817385501)
          ·
            refine ⟨12600908237255409306519563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33602421966014424817385501 12600908237255409306519563)
            ·
              refine ⟨18901362355883113959779345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12600908237255409306519563 18901362355883113959779345)
              ·
                refine ⟨14176021766912335469834509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18901362355883113959779345 14176021766912335469834509)
                ·
                  refine ⟨5316008162592125801187941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14176021766912335469834509 5316008162592125801187941)
                  ·
                    refine ⟨996751530486023587722739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5316008162592125801187941 996751530486023587722739)
                    ·
                      rfl

theorem cell23_5823500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_5823500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823500 prefixEnd_5823500 := by exact prefixLift 5823500
  have htrace : WordTrace (prefixWord ++ tailWord_5823500) baseStart_5823500 baseEnd_5823500 := by
    simpa [prefixWord, tailWord_5823500, baseEnd_5823500] using wordTrace_append hprefix tailTrace_5823500
  have hstable : (prefixWord ++ tailWord_5823500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823500).length < 2 ^ (prefixWord ++ tailWord_5823500).sum := by decide
  have hdescent : baseEnd_5823500 < baseStart_5823500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823530 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_5823530 : Nat := 118140960795 + 5823530 * 2 ^ 59
def prefixEnd_5823530 : Nat := 4983230072969 + 3 ^ 40 * 5823530 * 2
def baseEnd_5823530 : Nat := 332252221764189516199231

theorem tailTrace_5823530 : CollatzResearch.WordTrace tailWord_5823530 prefixEnd_5823530 332252221764189516199231 := by
  unfold tailWord_5823530
  simp only [CollatzResearch.WordTrace]
  refine ⟨53100397148088216146643011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141601059061568576391048029 53100397148088216146643011)
  ·
    refine ⟨79650595722132324219964517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53100397148088216146643011 79650595722132324219964517)
    ·
      refine ⟨14934486697899810791243347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79650595722132324219964517 14934486697899810791243347)
      ·
        refine ⟨22401730046849716186865021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14934486697899810791243347 22401730046849716186865021)
        ·
          refine ⟨8400648767568643570074383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22401730046849716186865021 8400648767568643570074383)
          ·
            refine ⟨12600973151352965355111575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400648767568643570074383 12600973151352965355111575)
            ·
              refine ⟨18901459727029448032667363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12600973151352965355111575 18901459727029448032667363)
              ·
                refine ⟨28352189590544172049001045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18901459727029448032667363 28352189590544172049001045)
                ·
                  refine ⟨332252221764189516199231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28352189590544172049001045 332252221764189516199231)
                  ·
                    rfl

theorem cell23_5823530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_5823530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823530 prefixEnd_5823530 := by exact prefixLift 5823530
  have htrace : WordTrace (prefixWord ++ tailWord_5823530) baseStart_5823530 baseEnd_5823530 := by
    simpa [prefixWord, tailWord_5823530, baseEnd_5823530] using wordTrace_append hprefix tailTrace_5823530
  have hstable : (prefixWord ++ tailWord_5823530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823530).length < 2 ^ (prefixWord ++ tailWord_5823530).sum := by decide
  have hdescent : baseEnd_5823530 < baseStart_5823530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823560 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_5823560 : Nat := 118140960795 + 5823560 * 2 ^ 59
def prefixEnd_5823560 : Nat := 4983230072969 + 3 ^ 40 * 5823560 * 2
def baseEnd_5823560 : Nat := 996761800099113509472647

theorem tailTrace_5823560 : CollatzResearch.WordTrace tailWord_5823560 prefixEnd_5823560 996761800099113509472647 := by
  unfold tailWord_5823560
  simp only [CollatzResearch.WordTrace]
  refine ⟨106201341391122089855082067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141601788521496119806776089 106201341391122089855082067)
  ·
    refine ⟨159302012086683134782623101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106201341391122089855082067 159302012086683134782623101)
    ·
      refine ⟨59738254532506175543483663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159302012086683134782623101 59738254532506175543483663)
      ·
        refine ⟨89607381798759263315225495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59738254532506175543483663 89607381798759263315225495)
        ·
          refine ⟨134411072698138894972838243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89607381798759263315225495 134411072698138894972838243)
          ·
            refine ⟨201616609047208342459257365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134411072698138894972838243 201616609047208342459257365)
            ·
              refine ⟨9450778549087891052777689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201616609047208342459257365 9450778549087891052777689)
              ·
                refine ⟨7088083911815918289583267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9450778549087891052777689 7088083911815918289583267)
                ·
                  refine ⟨10632125867723877434374901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088083911815918289583267 10632125867723877434374901)
                  ·
                    refine ⟨996761800099113509472647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10632125867723877434374901 996761800099113509472647)
                    ·
                      rfl

theorem cell23_5823560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_5823560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823560 prefixEnd_5823560 := by exact prefixLift 5823560
  have htrace : WordTrace (prefixWord ++ tailWord_5823560) baseStart_5823560 baseEnd_5823560 := by
    simpa [prefixWord, tailWord_5823560, baseEnd_5823560] using wordTrace_append hprefix tailTrace_5823560
  have hstable : (prefixWord ++ tailWord_5823560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823560).length < 2 ^ (prefixWord ++ tailWord_5823560).sum := by decide
  have hdescent : baseEnd_5823560 < baseStart_5823560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823573 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_5823573 : Nat := 118140960795 + 5823573 * 2 ^ 59
def prefixEnd_5823573 : Nat := 4983230072969 + 3 ^ 40 * 5823573 * 2
def baseEnd_5823573 : Nat := 996764025181949659185127

theorem tailTrace_5823573 : CollatzResearch.WordTrace tailWord_5823573 prefixEnd_5823573 996764025181949659185127 := by
  unfold tailWord_5823573
  simp only [CollatzResearch.WordTrace]
  refine ⟨212403156931197082930387373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141602104620798055286924915 212403156931197082930387373)
  ·
    refine ⟨79651183849198906098895265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212403156931197082930387373 79651183849198906098895265)
    ·
      refine ⟨59738387886899179574171449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79651183849198906098895265 59738387886899179574171449)
      ·
        refine ⟨44803790915174384680628587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59738387886899179574171449 44803790915174384680628587)
        ·
          refine ⟨67205686372761577020942881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44803790915174384680628587 67205686372761577020942881)
          ·
            refine ⟨50404264779571182765707161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67205686372761577020942881 50404264779571182765707161)
            ·
              refine ⟨37803198584678387074280371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50404264779571182765707161 37803198584678387074280371)
              ·
                refine ⟨56704797877017580611420557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37803198584678387074280371 56704797877017580611420557)
                ·
                  refine ⟨21264299203881592729282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56704797877017580611420557 21264299203881592729282709)
                  ·
                    refine ⟨996764025181949659185127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21264299203881592729282709 996764025181949659185127)
                    ·
                      rfl

theorem cell23_5823573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_5823573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823573 prefixEnd_5823573 := by exact prefixLift 5823573
  have htrace : WordTrace (prefixWord ++ tailWord_5823573) baseStart_5823573 baseEnd_5823573 := by
    simpa [prefixWord, tailWord_5823573, baseEnd_5823573] using wordTrace_append hprefix tailTrace_5823573
  have hstable : (prefixWord ++ tailWord_5823573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823573).length < 2 ^ (prefixWord ++ tailWord_5823573).sum := by decide
  have hdescent : baseEnd_5823573 < baseStart_5823573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823591 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_5823591 : Nat := 118140960795 + 5823591 * 2 ^ 59
def prefixEnd_5823591 : Nat := 4983230072969 + 3 ^ 40 * 5823591 * 2
def baseEnd_5823591 : Nat := 2990301318197629907130299

theorem tailTrace_5823591 : CollatzResearch.WordTrace tailWord_5823591 prefixEnd_5823591 2990301318197629907130299 := by
  unfold tailWord_5823591
  simp only [CollatzResearch.WordTrace]
  refine ⟨212403813445131872004542627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141602542296754581336361751 212403813445131872004542627)
  ·
    refine ⟨318605720167697808006813941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212403813445131872004542627 318605720167697808006813941)
    ·
      refine ⟨29869286265721669500638807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 318605720167697808006813941 29869286265721669500638807)
      ·
        refine ⟨44803929398582504250958211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29869286265721669500638807 44803929398582504250958211)
        ·
          refine ⟨67205894097873756376437317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44803929398582504250958211 67205894097873756376437317)
          ·
            refine ⟨12601105143351329320581997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67205894097873756376437317 12601105143351329320581997)
            ·
              refine ⟨4725414428756748495218249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12601105143351329320581997 4725414428756748495218249)
              ·
                refine ⟨3544060821567561371413687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725414428756748495218249 3544060821567561371413687)
                ·
                  refine ⟨5316091232351342057120531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544060821567561371413687 5316091232351342057120531)
                  ·
                    refine ⟨7974136848527013085680797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316091232351342057120531 7974136848527013085680797)
                    ·
                      refine ⟨2990301318197629907130299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974136848527013085680797 2990301318197629907130299)
                      ·
                        rfl

theorem cell23_5823591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_5823591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823591 prefixEnd_5823591 := by exact prefixLift 5823591
  have htrace : WordTrace (prefixWord ++ tailWord_5823591) baseStart_5823591 baseEnd_5823591 := by
    simpa [prefixWord, tailWord_5823591, baseEnd_5823591] using wordTrace_append hprefix tailTrace_5823591
  have hstable : (prefixWord ++ tailWord_5823591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823591).length < 2 ^ (prefixWord ++ tailWord_5823591).sum := by decide
  have hdescent : baseEnd_5823591 < baseStart_5823591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823593 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_5823593 : Nat := 118140960795 + 5823593 * 2 ^ 59
def prefixEnd_5823593 : Nat := 4983230072969 + 3 ^ 40 * 5823593 * 2
def baseEnd_5823593 : Nat := 2990302345158938899305289

theorem tailTrace_5823593 : CollatzResearch.WordTrace tailWord_5823593 prefixEnd_5823593 2990302345158938899305289 := by
  unfold tailWord_5823593
  simp only [CollatzResearch.WordTrace]
  refine ⟨212403886391124626346115433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141602590927416417564076955 212403886391124626346115433)
  ·
    refine ⟨159302914793343469759586575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212403886391124626346115433 159302914793343469759586575)
    ·
      refine ⟨238954372190015204639379863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159302914793343469759586575 238954372190015204639379863)
      ·
        refine ⟨358431558285022806959069795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238954372190015204639379863 358431558285022806959069795)
        ·
          refine ⟨537647337427534210438604693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358431558285022806959069795 537647337427534210438604693)
          ·
            refine ⟨25202218941915666114309595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 537647337427534210438604693 25202218941915666114309595)
            ·
              refine ⟨37803328412873499171464393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25202218941915666114309595 37803328412873499171464393)
              ·
                refine ⟨28352496309655124378598295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37803328412873499171464393 28352496309655124378598295)
                ·
                  refine ⟨42528744464482686567897443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28352496309655124378598295 42528744464482686567897443)
                  ·
                    refine ⟨63793116696724029851846165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42528744464482686567897443 63793116696724029851846165)
                    ·
                      refine ⟨2990302345158938899305289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63793116696724029851846165 2990302345158938899305289)
                      ·
                        rfl

theorem cell23_5823593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_5823593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823593 prefixEnd_5823593 := by exact prefixLift 5823593
  have htrace : WordTrace (prefixWord ++ tailWord_5823593) baseStart_5823593 baseEnd_5823593 := by
    simpa [prefixWord, tailWord_5823593, baseEnd_5823593] using wordTrace_append hprefix tailTrace_5823593
  have hstable : (prefixWord ++ tailWord_5823593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823593).length < 2 ^ (prefixWord ++ tailWord_5823593).sum := by decide
  have hdescent : baseEnd_5823593 < baseStart_5823593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823600 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_5823600 : Nat := 118140960795 + 5823600 * 2 ^ 59
def prefixEnd_5823600 : Nat := 4983230072969 + 3 ^ 40 * 5823600 * 2
def baseEnd_5823600 : Nat := 2990305939523520371917757

theorem tailTrace_5823600 : CollatzResearch.WordTrace tailWord_5823600 prefixEnd_5823600 2990305939523520371917757 := by
  unfold tailWord_5823600
  simp only [CollatzResearch.WordTrace]
  refine ⟨106202070851049633270810127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141602761134732844361080169 106202070851049633270810127)
  ·
    refine ⟨159303106276574449906215191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106202070851049633270810127 159303106276574449906215191)
    ·
      refine ⟨238954659414861674859322787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159303106276574449906215191 238954659414861674859322787)
      ·
        refine ⟨358431989122292512288984181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238954659414861674859322787 358431989122292512288984181)
        ·
          refine ⟨33602998980214923027092267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 358431989122292512288984181 33602998980214923027092267)
          ·
            refine ⟨50404498470322384540638401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33602998980214923027092267 50404498470322384540638401)
            ·
              refine ⟨37803373852741788405478801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50404498470322384540638401 37803373852741788405478801)
              ·
                refine ⟨28352530389556341304109101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37803373852741788405478801 28352530389556341304109101)
                ·
                  refine ⟨10632198896083627989040913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28352530389556341304109101 10632198896083627989040913)
                  ·
                    refine ⟨7974149172062720991780685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10632198896083627989040913 7974149172062720991780685)
                    ·
                      refine ⟨2990305939523520371917757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974149172062720991780685 2990305939523520371917757)
                      ·
                        rfl

theorem cell23_5823600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_5823600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823600 prefixEnd_5823600 := by exact prefixLift 5823600
  have htrace : WordTrace (prefixWord ++ tailWord_5823600) baseStart_5823600 baseEnd_5823600 := by
    simpa [prefixWord, tailWord_5823600, baseEnd_5823600] using wordTrace_append hprefix tailTrace_5823600
  have hstable : (prefixWord ++ tailWord_5823600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823600).length < 2 ^ (prefixWord ++ tailWord_5823600).sum := by decide
  have hdescent : baseEnd_5823600 < baseStart_5823600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823617 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5823617 : Nat := 118140960795 + 5823617 * 2 ^ 59
def prefixEnd_5823617 : Nat := 4983230072969 + 3 ^ 40 * 5823617 * 2
def baseEnd_5823617 : Nat := 2990314668694646805405179

theorem tailTrace_5823617 : CollatzResearch.WordTrace tailWord_5823617 prefixEnd_5823617 2990314668694646805405179 := by
  unfold tailWord_5823617
  simp only [CollatzResearch.WordTrace]
  refine ⟨212404761743037678444989105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141603174495358452296659403 212404761743037678444989105)
  ·
    refine ⟨159303571307278258833741829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212404761743037678444989105 159303571307278258833741829)
    ·
      refine ⟨29869419620114673531326593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159303571307278258833741829 29869419620114673531326593)
      ·
        refine ⟨22402064715086005148494945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29869419620114673531326593 22402064715086005148494945)
        ·
          refine ⟨16801548536314503861371209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22402064715086005148494945 16801548536314503861371209)
          ·
            refine ⟨12601161402235877896028407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16801548536314503861371209 12601161402235877896028407)
            ·
              refine ⟨18901742103353816844042611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12601161402235877896028407 18901742103353816844042611)
              ·
                refine ⟨28352613155030725266063917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18901742103353816844042611 28352613155030725266063917)
                ·
                  refine ⟨10632229933136521974773969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28352613155030725266063917 10632229933136521974773969)
                  ·
                    refine ⟨7974172449852391481080477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10632229933136521974773969 7974172449852391481080477)
                    ·
                      refine ⟨2990314668694646805405179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974172449852391481080477 2990314668694646805405179)
                      ·
                        rfl

theorem cell23_5823617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5823617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823617 prefixEnd_5823617 := by exact prefixLift 5823617
  have htrace : WordTrace (prefixWord ++ tailWord_5823617) baseStart_5823617 baseEnd_5823617 := by
    simpa [prefixWord, tailWord_5823617, baseEnd_5823617] using wordTrace_append hprefix tailTrace_5823617
  have hstable : (prefixWord ++ tailWord_5823617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823617).length < 2 ^ (prefixWord ++ tailWord_5823617).sum := by decide
  have hdescent : baseEnd_5823617 < baseStart_5823617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823663 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 8]
def baseStart_5823663 : Nat := 118140960795 + 5823663 * 2 ^ 59
def prefixEnd_5823663 : Nat := 4983230072969 + 3 ^ 40 * 5823663 * 2
def baseEnd_5823663 : Nat := 996779429601584541809989

theorem tailTrace_5823663 : CollatzResearch.WordTrace tailWord_5823663 prefixEnd_5823663 996779429601584541809989 := by
  unfold tailWord_5823663
  simp only [CollatzResearch.WordTrace]
  refine ⟨212406439500871028301163643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141604293000580685534109095 212406439500871028301163643)
  ·
    refine ⟨318609659251306542451745465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212406439500871028301163643 318609659251306542451745465)
    ·
      refine ⟨238957244438479906838809099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318609659251306542451745465 238957244438479906838809099)
      ·
        refine ⟨358435866657719860258213649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238957244438479906838809099 358435866657719860258213649)
        ·
          refine ⟨268826899993289895193660237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358435866657719860258213649 268826899993289895193660237)
          ·
            refine ⟨100810087497483710697622589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268826899993289895193660237 100810087497483710697622589)
            ·
              refine ⟨37803782811556391511608471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100810087497483710697622589 37803782811556391511608471)
              ·
                refine ⟨56705674217334587267412707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37803782811556391511608471 56705674217334587267412707)
                ·
                  refine ⟨85058511326001880901119061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56705674217334587267412707 85058511326001880901119061)
                  ·
                    refine ⟨996779429601584541809989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85058511326001880901119061 996779429601584541809989)
                    ·
                      rfl

theorem cell23_5823663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_5823663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823663 prefixEnd_5823663 := by exact prefixLift 5823663
  have htrace : WordTrace (prefixWord ++ tailWord_5823663) baseStart_5823663 baseEnd_5823663 := by
    simpa [prefixWord, tailWord_5823663, baseEnd_5823663] using wordTrace_append hprefix tailTrace_5823663
  have hstable : (prefixWord ++ tailWord_5823663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823663).length < 2 ^ (prefixWord ++ tailWord_5823663).sum := by decide
  have hdescent : baseEnd_5823663 < baseStart_5823663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823682 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5823682 : Nat := 118140960795 + 5823682 * 2 ^ 59
def prefixEnd_5823682 : Nat := 4983230072969 + 3 ^ 40 * 5823682 * 2
def baseEnd_5823682 : Nat := 2990348044937189051092381

theorem tailTrace_5823682 : CollatzResearch.WordTrace tailWord_5823682 prefixEnd_5823682 2990348044937189051092381 := by
  unfold tailWord_5823682
  simp only [CollatzResearch.WordTrace]
  refine ⟨53101783121950548636526325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141604754991868129697403533 53101783121950548636526325)
  ·
    refine ⟨4978292167682863934674343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53101783121950548636526325 4978292167682863934674343)
    ·
      refine ⟨7467438251524295902011515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978292167682863934674343 7467438251524295902011515)
      ·
        refine ⟨11201157377286443853017273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467438251524295902011515 11201157377286443853017273)
        ·
          refine ⟨8400868032964832889762955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11201157377286443853017273 8400868032964832889762955)
          ·
            refine ⟨12601302049447249334644433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400868032964832889762955 12601302049447249334644433)
            ·
              refine ⟨9450976537085437000983325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12601302049447249334644433 9450976537085437000983325)
              ·
                refine ⟨3544116201407038875368747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9450976537085437000983325 3544116201407038875368747)
                ·
                  refine ⟨5316174302110558313053121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544116201407038875368747 5316174302110558313053121)
                  ·
                    refine ⟨3987130726582918734789841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5316174302110558313053121 3987130726582918734789841)
                    ·
                      refine ⟨2990348044937189051092381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987130726582918734789841 2990348044937189051092381)
                      ·
                        rfl

theorem cell23_5823682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5823682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823682 prefixEnd_5823682 := by exact prefixLift 5823682
  have htrace : WordTrace (prefixWord ++ tailWord_5823682) baseStart_5823682 baseEnd_5823682 := by
    simpa [prefixWord, tailWord_5823682, baseEnd_5823682] using wordTrace_append hprefix tailTrace_5823682
  have hstable : (prefixWord ++ tailWord_5823682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823682).length < 2 ^ (prefixWord ++ tailWord_5823682).sum := by decide
  have hdescent : baseEnd_5823682 < baseStart_5823682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823777 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5823777 : Nat := 118140960795 + 5823777 * 2 ^ 59
def prefixEnd_5823777 : Nat := 4983230072969 + 3 ^ 40 * 5823777 * 2
def baseEnd_5823777 : Nat := 2990396825599366179404443

theorem tailTrace_5823777 : CollatzResearch.WordTrace tailWord_5823777 prefixEnd_5823777 2990396825599366179404443 := by
  unfold tailWord_5823777
  simp only [CollatzResearch.WordTrace]
  refine ⟨212410597422458025770813585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141607064948305350513875723 212410597422458025770813585)
  ·
    refine ⟨159307948066843519328110189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212410597422458025770813585 159307948066843519328110189)
    ·
      refine ⟨59740480525066319748041321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159307948066843519328110189 59740480525066319748041321)
      ·
        refine ⟨44805360393799739811030991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59740480525066319748041321 44805360393799739811030991)
        ·
          refine ⟨67208040590699609716546487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44805360393799739811030991 67208040590699609716546487)
          ·
            refine ⟨100812060886049414574819731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67208040590699609716546487 100812060886049414574819731)
            ·
              refine ⟨151218091329074121862229597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100812060886049414574819731 151218091329074121862229597)
              ·
                refine ⟨56706784248402795698336099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151218091329074121862229597 56706784248402795698336099)
                ·
                  refine ⟨85060176372604193547504149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56706784248402795698336099 85060176372604193547504149)
                  ·
                    refine ⟨3987195767465821572539257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85060176372604193547504149 3987195767465821572539257)
                    ·
                      refine ⟨2990396825599366179404443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987195767465821572539257 2990396825599366179404443)
                      ·
                        rfl

theorem cell23_5823777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5823777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823777 prefixEnd_5823777 := by exact prefixLift 5823777
  have htrace : WordTrace (prefixWord ++ tailWord_5823777) baseStart_5823777 baseEnd_5823777 := by
    simpa [prefixWord, tailWord_5823777, baseEnd_5823777] using wordTrace_append hprefix tailTrace_5823777
  have hstable : (prefixWord ++ tailWord_5823777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823777).length < 2 ^ (prefixWord ++ tailWord_5823777).sum := by decide
  have hdescent : baseEnd_5823777 < baseStart_5823777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823794 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_5823794 : Nat := 118140960795 + 5823794 * 2 ^ 59
def prefixEnd_5823794 : Nat := 4983230072969 + 3 ^ 40 * 5823794 * 2
def baseEnd_5823794 : Nat := 2990405554770492612891865

theorem tailTrace_5823794 : CollatzResearch.WordTrace tailWord_5823794 prefixEnd_5823794 2990405554770492612891865 := by
  unfold tailWord_5823794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53102804365849109418545609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141607478308930958449454957 53102804365849109418545609)
  ·
    refine ⟨39827103274386832063909207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53102804365849109418545609 39827103274386832063909207)
    ·
      refine ⟨59740654911580248095863811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39827103274386832063909207 59740654911580248095863811)
      ·
        refine ⟨89610982367370372143795717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59740654911580248095863811 89610982367370372143795717)
        ·
          refine ⟨16802059193881944776961697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89610982367370372143795717 16802059193881944776961697)
          ·
            refine ⟨12601544395411458582721273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16802059193881944776961697 12601544395411458582721273)
            ·
              refine ⟨9451158296558593937040955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12601544395411458582721273 9451158296558593937040955)
              ·
                refine ⟨14176737444837890905561433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9451158296558593937040955 14176737444837890905561433)
                ·
                  refine ⟨10632553083628418179171075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14176737444837890905561433 10632553083628418179171075)
                  ·
                    refine ⟨15948829625442627268756613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10632553083628418179171075 15948829625442627268756613)
                    ·
                      refine ⟨2990405554770492612891865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15948829625442627268756613 2990405554770492612891865)
                      ·
                        rfl

theorem cell23_5823794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_5823794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823794 prefixEnd_5823794 := by exact prefixLift 5823794
  have htrace : WordTrace (prefixWord ++ tailWord_5823794) baseStart_5823794 baseEnd_5823794 := by
    simpa [prefixWord, tailWord_5823794, baseEnd_5823794] using wordTrace_append hprefix tailTrace_5823794
  have hstable : (prefixWord ++ tailWord_5823794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823794).length < 2 ^ (prefixWord ++ tailWord_5823794).sum := by decide
  have hdescent : baseEnd_5823794 < baseStart_5823794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823844 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_5823844 : Nat := 118140960795 + 5823844 * 2 ^ 59
def prefixEnd_5823844 : Nat := 4983230072969 + 3 ^ 40 * 5823844 * 2
def baseEnd_5823844 : Nat := 2990431228803217417266635

theorem tailTrace_5823844 : CollatzResearch.WordTrace tailWord_5823844 prefixEnd_5823844 2990431228803217417266635 := by
  unfold tailWord_5823844
  simp only [CollatzResearch.WordTrace]
  refine ⟨106206520556607648106751293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141608694075476864142335057 106206520556607648106751293)
  ·
    refine ⟨39827445208727868040031735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106206520556607648106751293 39827445208727868040031735)
    ·
      refine ⟨59741167813091802060047603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39827445208727868040031735 59741167813091802060047603)
      ·
        refine ⟨89611751719637703090071405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59741167813091802060047603 89611751719637703090071405)
        ·
          refine ⟨33604406894864138658776777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89611751719637703090071405 33604406894864138658776777)
          ·
            refine ⟨25203305171148103994082583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33604406894864138658776777 25203305171148103994082583)
            ·
              refine ⟨37804957756722155991123875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25203305171148103994082583 37804957756722155991123875)
              ·
                refine ⟨56707436635083233986685813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37804957756722155991123875 56707436635083233986685813)
                ·
                  refine ⟨5316322184539053186251795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56707436635083233986685813 5316322184539053186251795)
                  ·
                    refine ⟨7974483276808579779377693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316322184539053186251795 7974483276808579779377693)
                    ·
                      refine ⟨2990431228803217417266635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974483276808579779377693 2990431228803217417266635)
                      ·
                        rfl

theorem cell23_5823844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_5823844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823844 prefixEnd_5823844 := by exact prefixLift 5823844
  have htrace : WordTrace (prefixWord ++ tailWord_5823844) baseStart_5823844 baseEnd_5823844 := by
    simpa [prefixWord, tailWord_5823844, baseEnd_5823844] using wordTrace_append hprefix tailTrace_5823844
  have hstable : (prefixWord ++ tailWord_5823844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823844).length < 2 ^ (prefixWord ++ tailWord_5823844).sum := by decide
  have hdescent : baseEnd_5823844 < baseStart_5823844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823848 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5823848 : Nat := 118140960795 + 5823848 * 2 ^ 59
def prefixEnd_5823848 : Nat := 4983230072969 + 3 ^ 40 * 5823848 * 2
def baseEnd_5823848 : Nat := 2990433282725835401616617

theorem tailTrace_5823848 : CollatzResearch.WordTrace tailWord_5823848 prefixEnd_5823848 2990433282725835401616617 := by
  unfold tailWord_5823848
  simp only [CollatzResearch.WordTrace]
  refine ⟨106206593502600402448324099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141608791336800536597765465 106206593502600402448324099)
  ·
    refine ⟨159309890253900603672486149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106206593502600402448324099 159309890253900603672486149)
    ·
      refine ⟨29870604422606363188591153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159309890253900603672486149 29870604422606363188591153)
      ·
        refine ⟨22402953316954772391443365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29870604422606363188591153 22402953316954772391443365)
        ·
          refine ⟨4200553746929019823395631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22402953316954772391443365 4200553746929019823395631)
          ·
            refine ⟨6300830620393529735093447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200553746929019823395631 6300830620393529735093447)
            ·
              refine ⟨9451245930590294602640171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300830620393529735093447 9451245930590294602640171)
              ·
                refine ⟨14176868895885441903960257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9451245930590294602640171 14176868895885441903960257)
                ·
                  refine ⟨10632651671914081427970193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14176868895885441903960257 10632651671914081427970193)
                  ·
                    refine ⟨7974488753935561070977645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10632651671914081427970193 7974488753935561070977645)
                    ·
                      refine ⟨2990433282725835401616617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974488753935561070977645 2990433282725835401616617)
                      ·
                        rfl

theorem cell23_5823848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5823848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823848 prefixEnd_5823848 := by exact prefixLift 5823848
  have htrace : WordTrace (prefixWord ++ tailWord_5823848) baseStart_5823848 baseEnd_5823848 := by
    simpa [prefixWord, tailWord_5823848, baseEnd_5823848] using wordTrace_append hprefix tailTrace_5823848
  have hstable : (prefixWord ++ tailWord_5823848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823848).length < 2 ^ (prefixWord ++ tailWord_5823848).sum := by decide
  have hdescent : baseEnd_5823848 < baseStart_5823848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823897 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5823897 : Nat := 118140960795 + 5823897 * 2 ^ 59
def prefixEnd_5823897 : Nat := 4983230072969 + 3 ^ 40 * 5823897 * 2
def baseEnd_5823897 : Nat := 2990458443277905709903891

theorem tailTrace_5823897 : CollatzResearch.WordTrace tailWord_5823897 prefixEnd_5823897 2990458443277905709903891 := by
  unfold tailWord_5823897
  simp only [CollatzResearch.WordTrace]
  refine ⟨212414974182023286265181945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141609982788015524176787963 212414974182023286265181945)
  ·
    refine ⟨159311230636517464698886459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212414974182023286265181945 159311230636517464698886459)
    ·
      refine ⟨238966845954776197048329689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159311230636517464698886459 238966845954776197048329689)
      ·
        refine ⟨179225134466082147786247267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238966845954776197048329689 179225134466082147786247267)
        ·
          refine ⟨268837701699123221679370901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179225134466082147786247267 268837701699123221679370901)
          ·
            refine ⟨12601767267146401016220511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 268837701699123221679370901 12601767267146401016220511)
            ·
              refine ⟨18902650900719601524330767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12601767267146401016220511 18902650900719601524330767)
              ·
                refine ⟨28353976351079402286496151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18902650900719601524330767 28353976351079402286496151)
                ·
                  refine ⟨42530964526619103429744227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28353976351079402286496151 42530964526619103429744227)
                  ·
                    refine ⟨63796446789928655144616341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42530964526619103429744227 63796446789928655144616341)
                    ·
                      refine ⟨2990458443277905709903891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63796446789928655144616341 2990458443277905709903891)
                      ·
                        rfl

theorem cell23_5823897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5823897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823897 prefixEnd_5823897 := by exact prefixLift 5823897
  have htrace : WordTrace (prefixWord ++ tailWord_5823897) baseStart_5823897 baseEnd_5823897 := by
    simpa [prefixWord, tailWord_5823897, baseEnd_5823897] using wordTrace_append hprefix tailTrace_5823897
  have hstable : (prefixWord ++ tailWord_5823897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823897).length < 2 ^ (prefixWord ++ tailWord_5823897).sum := by decide
  have hdescent : baseEnd_5823897 < baseStart_5823897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823901 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5823901 : Nat := 118140960795 + 5823901 * 2 ^ 59
def prefixEnd_5823901 : Nat := 4983230072969 + 3 ^ 40 * 5823901 * 2
def baseEnd_5823901 : Nat := 2990460497200523694253873

theorem tailTrace_5823901 : CollatzResearch.WordTrace tailWord_5823901 prefixEnd_5823901 2990460497200523694253873 := by
  unfold tailWord_5823901
  simp only [CollatzResearch.WordTrace]
  refine ⟨212415120074008794948327557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141610080049339196632218371 212415120074008794948327557)
  ·
    refine ⟨39827835013876649052811417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212415120074008794948327557 39827835013876649052811417)
    ·
      refine ⟨29870876260407486789608563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39827835013876649052811417 29870876260407486789608563)
      ·
        refine ⟨44806314390611230184412845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29870876260407486789608563 44806314390611230184412845)
        ·
          refine ⟨16802367896479211319154817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44806314390611230184412845 16802367896479211319154817)
          ·
            refine ⟨12601775922359408489366113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16802367896479211319154817 12601775922359408489366113)
            ·
              refine ⟨9451331941769556367024585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12601775922359408489366113 9451331941769556367024585)
              ·
                refine ⟨7088498956327167275268439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9451331941769556367024585 7088498956327167275268439)
                ·
                  refine ⟨10632748434490750912902659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088498956327167275268439 10632748434490750912902659)
                  ·
                    refine ⟨15949122651736126369353989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10632748434490750912902659 15949122651736126369353989)
                    ·
                      refine ⟨2990460497200523694253873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15949122651736126369353989 2990460497200523694253873)
                      ·
                        rfl

theorem cell23_5823901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5823901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823901 prefixEnd_5823901 := by exact prefixLift 5823901
  have htrace : WordTrace (prefixWord ++ tailWord_5823901) baseStart_5823901 baseEnd_5823901 := by
    simpa [prefixWord, tailWord_5823901, baseEnd_5823901] using wordTrace_append hprefix tailTrace_5823901
  have hstable : (prefixWord ++ tailWord_5823901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823901).length < 2 ^ (prefixWord ++ tailWord_5823901).sum := by decide
  have hdescent : baseEnd_5823901 < baseStart_5823901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823912 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5823912 : Nat := 118140960795 + 5823912 * 2 ^ 59
def prefixEnd_5823912 : Nat := 4983230072969 + 3 ^ 40 * 5823912 * 2
def baseEnd_5823912 : Nat := 2990466145487723151216323

theorem tailTrace_5823912 : CollatzResearch.WordTrace tailWord_5823912 prefixEnd_5823912 2990466145487723151216323 := by
  unfold tailWord_5823912
  simp only [CollatzResearch.WordTrace]
  refine ⟨106207760638484471913488995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141610347517979295884651993 106207760638484471913488995)
  ·
    refine ⟨159311640957726707870233493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106207760638484471913488995 159311640957726707870233493)
    ·
      refine ⟨7467733169893439431417195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159311640957726707870233493 7467733169893439431417195)
      ·
        refine ⟨11201599754840159147125793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467733169893439431417195 11201599754840159147125793)
        ·
          refine ⟨8401199816130119360344345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11201599754840159147125793 8401199816130119360344345)
          ·
            refine ⟨6300899862097589520258259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8401199816130119360344345 6300899862097589520258259)
            ·
              refine ⟨9451349793146384280387389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300899862097589520258259 9451349793146384280387389)
              ·
                refine ⟨3544256172429894105145271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9451349793146384280387389 3544256172429894105145271)
                ·
                  refine ⟨5316384258644841157717907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544256172429894105145271 5316384258644841157717907)
                  ·
                    refine ⟨7974576387967261736576861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316384258644841157717907 7974576387967261736576861)
                    ·
                      refine ⟨2990466145487723151216323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974576387967261736576861 2990466145487723151216323)
                      ·
                        rfl

theorem cell23_5823912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5823912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823912 prefixEnd_5823912 := by exact prefixLift 5823912
  have htrace : WordTrace (prefixWord ++ tailWord_5823912) baseStart_5823912 baseEnd_5823912 := by
    simpa [prefixWord, tailWord_5823912, baseEnd_5823912] using wordTrace_append hprefix tailTrace_5823912
  have hstable : (prefixWord ++ tailWord_5823912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823912).length < 2 ^ (prefixWord ++ tailWord_5823912).sum := by decide
  have hdescent : baseEnd_5823912 < baseStart_5823912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5823961 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 3, 3, 2]
def baseStart_5823961 : Nat := 118140960795 + 5823961 * 2 ^ 59
def prefixEnd_5823961 : Nat := 4983230072969 + 3 ^ 40 * 5823961 * 2
def baseEnd_5823961 : Nat := 2990491306039793459503597

theorem tailTrace_5823961 : CollatzResearch.WordTrace tailWord_5823961 prefixEnd_5823961 2990491306039793459503597 := by
  unfold tailWord_5823961
  simp only [CollatzResearch.WordTrace]
  refine ⟨212417308453791425195511737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141611538969194283463674491 212417308453791425195511737)
  ·
    refine ⟨159312981340343568896633803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212417308453791425195511737 159312981340343568896633803)
    ·
      refine ⟨238969472010515353344950705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159312981340343568896633803 238969472010515353344950705)
      ·
        refine ⟨179227104007886515008713029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238969472010515353344950705 179227104007886515008713029)
        ·
          refine ⟨33605082001478721564133693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179227104007886515008713029 33605082001478721564133693)
          ·
            refine ⟨12601905750554520586550135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33605082001478721564133693 12601905750554520586550135)
            ·
              refine ⟨18902858625831780879825203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12601905750554520586550135 18902858625831780879825203)
              ·
                refine ⟨28354287938747671319737805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18902858625831780879825203 28354287938747671319737805)
                ·
                  refine ⟨10632857977030376744901677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28354287938747671319737805 10632857977030376744901677)
                  ·
                    refine ⟨3987321741386391279338129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10632857977030376744901677 3987321741386391279338129)
                    ·
                      refine ⟨2990491306039793459503597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987321741386391279338129 2990491306039793459503597)
                      ·
                        rfl

theorem cell23_5823961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_5823961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5823961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5823961 prefixEnd_5823961 := by exact prefixLift 5823961
  have htrace : WordTrace (prefixWord ++ tailWord_5823961) baseStart_5823961 baseEnd_5823961 := by
    simpa [prefixWord, tailWord_5823961, baseEnd_5823961] using wordTrace_append hprefix tailTrace_5823961
  have hstable : (prefixWord ++ tailWord_5823961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5823961).length < 2 ^ (prefixWord ++ tailWord_5823961).sum := by decide
  have hdescent : baseEnd_5823961 < baseStart_5823961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5823961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824008 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_5824008 : Nat := 118140960795 + 5824008 * 2 ^ 59
def prefixEnd_5824008 : Nat := 4983230072969 + 3 ^ 40 * 5824008 * 2
def baseEnd_5824008 : Nat := 2990515439630554775615881

theorem tailTrace_5824008 : CollatzResearch.WordTrace tailWord_5824008 prefixEnd_5824008 2990515439630554775615881 := by
  unfold tailWord_5824008
  simp only [CollatzResearch.WordTrace]
  refine ⟨106209511342310576111236339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141612681789747434814981785 106209511342310576111236339)
  ·
    refine ⟨159314267013465864166854509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106209511342310576111236339 159314267013465864166854509)
    ·
      refine ⟨59742850130049699062570441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159314267013465864166854509 59742850130049699062570441)
      ·
        refine ⟨44807137597537274296927831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59742850130049699062570441 44807137597537274296927831)
        ·
          refine ⟨67210706396305911445391747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44807137597537274296927831 67210706396305911445391747)
          ·
            refine ⟨100816059594458867168087621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67210706396305911445391747 100816059594458867168087621)
            ·
              refine ⟨18903011173961037594016429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100816059594458867168087621 18903011173961037594016429)
              ·
                refine ⟨7088629190235389097756161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18903011173961037594016429 7088629190235389097756161)
                ·
                  refine ⟨5316471892676541823317121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7088629190235389097756161 5316471892676541823317121)
                  ·
                    refine ⟨3987353919507406367487841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5316471892676541823317121 3987353919507406367487841)
                    ·
                      refine ⟨2990515439630554775615881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987353919507406367487841 2990515439630554775615881)
                      ·
                        rfl

theorem cell23_5824008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_5824008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824008 prefixEnd_5824008 := by exact prefixLift 5824008
  have htrace : WordTrace (prefixWord ++ tailWord_5824008) baseStart_5824008 baseEnd_5824008 := by
    simpa [prefixWord, tailWord_5824008, baseEnd_5824008] using wordTrace_append hprefix tailTrace_5824008
  have hstable : (prefixWord ++ tailWord_5824008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824008).length < 2 ^ (prefixWord ++ tailWord_5824008).sum := by decide
  have hdescent : baseEnd_5824008 < baseStart_5824008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824101 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_5824101 : Nat := 118140960795 + 5824101 * 2 ^ 59
def prefixEnd_5824101 : Nat := 4983230072969 + 3 ^ 40 * 5824101 * 2
def baseEnd_5824101 : Nat := 2990563193331422911752953

theorem tailTrace_5824101 : CollatzResearch.WordTrace tailWord_5824101 prefixEnd_5824101 2990563193331422911752953 := by
  unfold tailWord_5824101
  simp only [CollatzResearch.WordTrace]
  refine ⟨212422414673284229105608157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141614943115522819403738771 212422414673284229105608157)
  ·
    refine ⟨79658405502481585914603059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212422414673284229105608157 79658405502481585914603059)
    ·
      refine ⟨119487608253722378871904589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79658405502481585914603059 119487608253722378871904589)
      ·
        refine ⟨44807853095145892076964221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119487608253722378871904589 44807853095145892076964221)
        ·
          refine ⟨16802944910679709528861583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44807853095145892076964221 16802944910679709528861583)
          ·
            refine ⟨25204417366019564293292375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802944910679709528861583 25204417366019564293292375)
            ·
              refine ⟨37806626049029346439938563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25204417366019564293292375 37806626049029346439938563)
              ·
                refine ⟨56709939073544019659907845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37806626049029346439938563 56709939073544019659907845)
                ·
                  refine ⟨10633113576289503686232721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56709939073544019659907845 10633113576289503686232721)
                  ·
                    refine ⟨7974835182217127764674541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10633113576289503686232721 7974835182217127764674541)
                    ·
                      refine ⟨2990563193331422911752953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974835182217127764674541 2990563193331422911752953)
                      ·
                        rfl

theorem cell23_5824101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_5824101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824101 prefixEnd_5824101 := by exact prefixLift 5824101
  have htrace : WordTrace (prefixWord ++ tailWord_5824101) baseStart_5824101 baseEnd_5824101 := by
    simpa [prefixWord, tailWord_5824101, baseEnd_5824101] using wordTrace_append hprefix tailTrace_5824101
  have hstable : (prefixWord ++ tailWord_5824101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824101).length < 2 ^ (prefixWord ++ tailWord_5824101).sum := by decide
  have hdescent : baseEnd_5824101 < baseStart_5824101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824131 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 3]
def baseStart_5824131 : Nat := 118140960795 + 5824131 * 2 ^ 59
def prefixEnd_5824131 : Nat := 4983230072969 + 3 ^ 40 * 5824131 * 2
def baseEnd_5824131 : Nat := 2990578597751057794377815

theorem tailTrace_5824131 : CollatzResearch.WordTrace tailWord_5824131 prefixEnd_5824131 2990578597751057794377815 := by
  unfold tailWord_5824131
  simp only [CollatzResearch.WordTrace]
  refine ⟨212423508863175544229200247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141615672575450362819466831 212423508863175544229200247)
  ·
    refine ⟨318635263294763316343800371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212423508863175544229200247 318635263294763316343800371)
    ·
      refine ⟨477952894942144974515700557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318635263294763316343800371 477952894942144974515700557)
      ·
        refine ⟨179232335603304365443387709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477952894942144974515700557 179232335603304365443387709)
        ·
          refine ⟨67212125851239137041270391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179232335603304365443387709 67212125851239137041270391)
          ·
            refine ⟨100818188776858705561905587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67212125851239137041270391 100818188776858705561905587)
            ·
              refine ⟨151227283165288058342858381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100818188776858705561905587 151227283165288058342858381)
              ·
                refine ⟨56710231186983021878571893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151227283165288058342858381 56710231186983021878571893)
                ·
                  refine ⟨5316584173779658301116115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56710231186983021878571893 5316584173779658301116115)
                  ·
                    refine ⟨7974876260669487451674173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316584173779658301116115 7974876260669487451674173)
                    ·
                      refine ⟨2990578597751057794377815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974876260669487451674173 2990578597751057794377815)
                      ·
                        rfl

theorem cell23_5824131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_5824131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824131 prefixEnd_5824131 := by exact prefixLift 5824131
  have htrace : WordTrace (prefixWord ++ tailWord_5824131) baseStart_5824131 baseEnd_5824131 := by
    simpa [prefixWord, tailWord_5824131, baseEnd_5824131] using wordTrace_append hprefix tailTrace_5824131
  have hstable : (prefixWord ++ tailWord_5824131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824131).length < 2 ^ (prefixWord ++ tailWord_5824131).sum := by decide
  have hdescent : baseEnd_5824131 < baseStart_5824131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824159 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 1, 4]
def baseStart_5824159 : Nat := 118140960795 + 5824159 * 2 ^ 59
def prefixEnd_5824159 : Nat := 4983230072969 + 3 ^ 40 * 5824159 * 2
def baseEnd_5824159 : Nat := 996864325069794561609229

theorem tailTrace_5824159 : CollatzResearch.WordTrace tailWord_5824159 prefixEnd_5824159 996864325069794561609229 := by
  unfold tailWord_5824159
  simp only [CollatzResearch.WordTrace]
  refine ⟨212424530107074105011219531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141616353404716070007479687 212424530107074105011219531)
  ·
    refine ⟨318636795160611157516829297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212424530107074105011219531 318636795160611157516829297)
    ·
      refine ⟨238977596370458368137621973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318636795160611157516829297 238977596370458368137621973)
      ·
        refine ⟨5601037414932618003225515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 238977596370458368137621973 5601037414932618003225515)
        ·
          refine ⟨8401556122398927004838273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601037414932618003225515 8401556122398927004838273)
          ·
            refine ⟨6301167091799195253628705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8401556122398927004838273 6301167091799195253628705)
            ·
              refine ⟨4725875318849396440221529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301167091799195253628705 4725875318849396440221529)
              ·
                refine ⟨3544406489137047330166147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725875318849396440221529 3544406489137047330166147)
                ·
                  refine ⟨5316609733705570995249221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544406489137047330166147 5316609733705570995249221)
                  ·
                    refine ⟨996864325069794561609229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5316609733705570995249221 996864325069794561609229)
                    ·
                      rfl

theorem cell23_5824159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 4].length) (baseStart_5824159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824159 prefixEnd_5824159 := by exact prefixLift 5824159
  have htrace : WordTrace (prefixWord ++ tailWord_5824159) baseStart_5824159 baseEnd_5824159 := by
    simpa [prefixWord, tailWord_5824159, baseEnd_5824159] using wordTrace_append hprefix tailTrace_5824159
  have hstable : (prefixWord ++ tailWord_5824159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824159).length < 2 ^ (prefixWord ++ tailWord_5824159).sum := by decide
  have hdescent : baseEnd_5824159 < baseStart_5824159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824182 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5824182 : Nat := 118140960795 + 5824182 * 2 ^ 59
def prefixEnd_5824182 : Nat := 4983230072969 + 3 ^ 40 * 5824182 * 2
def baseEnd_5824182 : Nat := 2990604785264437094840081

theorem tailTrace_5824182 : CollatzResearch.WordTrace tailWord_5824182 prefixEnd_5824182 2990604785264437094840081 := by
  unfold tailWord_5824182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276585561624423746206675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141616912657327186626204533 13276585561624423746206675)
  ·
    refine ⟨19914878342436635619310013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276585561624423746206675 19914878342436635619310013)
    ·
      refine ⟨7468079378413738357241255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19914878342436635619310013 7468079378413738357241255)
      ·
        refine ⟨11202119067620607535861883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468079378413738357241255 11202119067620607535861883)
        ·
          refine ⟨16803178601430911303792825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202119067620607535861883 16803178601430911303792825)
          ·
            refine ⟨12602383951073183477844619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16803178601430911303792825 12602383951073183477844619)
            ·
              refine ⟨18903575926609775216766929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12602383951073183477844619 18903575926609775216766929)
              ·
                refine ⟨14177681944957331412575197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18903575926609775216766929 14177681944957331412575197)
                ·
                  refine ⟨5316630729358999279715699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14177681944957331412575197 5316630729358999279715699)
                  ·
                    refine ⟨7974946094038498919573549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316630729358999279715699 7974946094038498919573549)
                    ·
                      refine ⟨2990604785264437094840081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974946094038498919573549 2990604785264437094840081)
                      ·
                        rfl

theorem cell23_5824182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5824182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824182 prefixEnd_5824182 := by exact prefixLift 5824182
  have htrace : WordTrace (prefixWord ++ tailWord_5824182) baseStart_5824182 baseEnd_5824182 := by
    simpa [prefixWord, tailWord_5824182, baseEnd_5824182] using wordTrace_append hprefix tailTrace_5824182
  have hstable : (prefixWord ++ tailWord_5824182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824182).length < 2 ^ (prefixWord ++ tailWord_5824182).sum := by decide
  have hdescent : baseEnd_5824182 < baseStart_5824182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824184 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_5824184 : Nat := 118140960795 + 5824184 * 2 ^ 59
def prefixEnd_5824184 : Nat := 4983230072969 + 3 ^ 40 * 5824184 * 2
def baseEnd_5824184 : Nat := 2990605812225746087015071

theorem tailTrace_5824184 : CollatzResearch.WordTrace tailWord_5824184 prefixEnd_5824184 2990605812225746087015071 := by
  unfold tailWord_5824184
  simp only [CollatzResearch.WordTrace]
  refine ⟨106212720965991767140439803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141616961287989022853919737 106212720965991767140439803)
  ·
    refine ⟨159319081448987650710659705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106212720965991767140439803 159319081448987650710659705)
    ·
      refine ⟨119489311086740738032994779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159319081448987650710659705 119489311086740738032994779)
      ·
        refine ⟨179233966630111107049492169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119489311086740738032994779 179233966630111107049492169)
        ·
          refine ⟨134425474972583330287119127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179233966630111107049492169 134425474972583330287119127)
          ·
            refine ⟨201638212458874995430678691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134425474972583330287119127 201638212458874995430678691)
            ·
              refine ⟨302457318688312493146018037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201638212458874995430678691 302457318688312493146018037)
              ·
                refine ⟨28355373627029296232439191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302457318688312493146018037 28355373627029296232439191)
                ·
                  refine ⟨42533060440543944348658787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28355373627029296232439191 42533060440543944348658787)
                  ·
                    refine ⟨63799590660815916522988181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42533060440543944348658787 63799590660815916522988181)
                    ·
                      refine ⟨2990605812225746087015071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63799590660815916522988181 2990605812225746087015071)
                      ·
                        rfl

theorem cell23_5824184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_5824184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824184 prefixEnd_5824184 := by exact prefixLift 5824184
  have htrace : WordTrace (prefixWord ++ tailWord_5824184) baseStart_5824184 baseEnd_5824184 := by
    simpa [prefixWord, tailWord_5824184, baseEnd_5824184] using wordTrace_append hprefix tailTrace_5824184
  have hstable : (prefixWord ++ tailWord_5824184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824184).length < 2 ^ (prefixWord ++ tailWord_5824184).sum := by decide
  have hdescent : baseEnd_5824184 < baseStart_5824184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824191 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_5824191 : Nat := 118140960795 + 5824191 * 2 ^ 59
def prefixEnd_5824191 : Nat := 4983230072969 + 3 ^ 40 * 5824191 * 2
def baseEnd_5824191 : Nat := 2990609406590327559627539

theorem tailTrace_5824191 : CollatzResearch.WordTrace tailWord_5824191 prefixEnd_5824191 2990609406590327559627539 := by
  unfold tailWord_5824191
  simp only [CollatzResearch.WordTrace]
  refine ⟨212425697242958174476384427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141617131495305449650922951 212425697242958174476384427)
  ·
    refine ⟨318638545864437261714576641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212425697242958174476384427 318638545864437261714576641)
    ·
      refine ⟨238978909398327946285932481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318638545864437261714576641 238978909398327946285932481)
      ·
        refine ⟨179234182048745959714449361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238978909398327946285932481 179234182048745959714449361)
        ·
          refine ⟨134425636536559469785837021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179234182048745959714449361 134425636536559469785837021)
          ·
            refine ⟨50409613701209801169688883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134425636536559469785837021 50409613701209801169688883)
            ·
              refine ⟨75614420551814701754533325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50409613701209801169688883 75614420551814701754533325)
              ·
                refine ⟨28355407706930513157949997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75614420551814701754533325 28355407706930513157949997)
                ·
                  refine ⟨10633277890098942434231249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28355407706930513157949997 10633277890098942434231249)
                  ·
                    refine ⟨7974958417574206825673437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10633277890098942434231249 7974958417574206825673437)
                    ·
                      refine ⟨2990609406590327559627539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7974958417574206825673437 2990609406590327559627539)
                      ·
                        rfl

theorem cell23_5824191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_5824191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824191 prefixEnd_5824191 := by exact prefixLift 5824191
  have htrace : WordTrace (prefixWord ++ tailWord_5824191) baseStart_5824191 baseEnd_5824191 := by
    simpa [prefixWord, tailWord_5824191, baseEnd_5824191] using wordTrace_append hprefix tailTrace_5824191
  have hstable : (prefixWord ++ tailWord_5824191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824191).length < 2 ^ (prefixWord ++ tailWord_5824191).sum := by decide
  have hdescent : baseEnd_5824191 < baseStart_5824191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824202 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_5824202 : Nat := 118140960795 + 5824202 * 2 ^ 59
def prefixEnd_5824202 : Nat := 4983230072969 + 3 ^ 40 * 5824202 * 2
def baseEnd_5824202 : Nat := 996871684959175672196663

theorem tailTrace_5824202 : CollatzResearch.WordTrace tailWord_5824202 prefixEnd_5824202 996871684959175672196663 := by
  unfold tailWord_5824202
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106524611479580838758715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141617398963945548903356573 53106524611479580838758715)
  ·
    refine ⟨79659786917219371258138073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53106524611479580838758715 79659786917219371258138073)
    ·
      refine ⟨59744840187914528443603555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79659786917219371258138073 59744840187914528443603555)
      ·
        refine ⟨89617260281871792665405333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59744840187914528443603555 89617260281871792665405333)
        ·
          refine ⟨4200809075712740281190875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89617260281871792665405333 4200809075712740281190875)
          ·
            refine ⟨6301213613569110421786313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200809075712740281190875 6301213613569110421786313)
            ·
              refine ⟨4725910210176832816339735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301213613569110421786313 4725910210176832816339735)
              ·
                refine ⟨7088865315265249224509603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725910210176832816339735 7088865315265249224509603)
                ·
                  refine ⟨10633297972897873836764405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7088865315265249224509603 10633297972897873836764405)
                  ·
                    refine ⟨996871684959175672196663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10633297972897873836764405 996871684959175672196663)
                    ·
                      rfl

theorem cell23_5824202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_5824202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824202 prefixEnd_5824202 := by exact prefixLift 5824202
  have htrace : WordTrace (prefixWord ++ tailWord_5824202) baseStart_5824202 baseEnd_5824202 := by
    simpa [prefixWord, tailWord_5824202, baseEnd_5824202] using wordTrace_append hprefix tailTrace_5824202
  have hstable : (prefixWord ++ tailWord_5824202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824202).length < 2 ^ (prefixWord ++ tailWord_5824202).sum := by decide
  have hdescent : baseEnd_5824202 < baseStart_5824202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824224 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_5824224 : Nat := 118140960795 + 5824224 * 2 ^ 59
def prefixEnd_5824224 : Nat := 4983230072969 + 3 ^ 40 * 5824224 * 2
def baseEnd_5824224 : Nat := 996875450483975310171629

theorem tailTrace_5824224 : CollatzResearch.WordTrace tailWord_5824224 prefixEnd_5824224 996875450483975310171629 := by
  unfold tailWord_5824224
  simp only [CollatzResearch.WordTrace]
  refine ⟨106213450425919310556167863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141617933901225747408223817 106213450425919310556167863)
  ·
    refine ⟨159320175638878965834251795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106213450425919310556167863 159320175638878965834251795)
    ·
      refine ⟨238980263458318448751377693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159320175638878965834251795 238980263458318448751377693)
      ·
        refine ⟨89617598796869418281766635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238980263458318448751377693 89617598796869418281766635)
        ·
          refine ⟨134426398195304127422649953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89617598796869418281766635 134426398195304127422649953)
          ·
            refine ⟨100819798646478095566987465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134426398195304127422649953 100819798646478095566987465)
            ·
              refine ⟨75614848984858571675240599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100819798646478095566987465 75614848984858571675240599)
              ·
                refine ⟨113422273477287857512860899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75614848984858571675240599 113422273477287857512860899)
                ·
                  refine ⟨170133410215931786269291349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113422273477287857512860899 170133410215931786269291349)
                  ·
                    refine ⟨996875450483975310171629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170133410215931786269291349 996875450483975310171629)
                    ·
                      rfl

theorem cell23_5824224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_5824224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824224 prefixEnd_5824224 := by exact prefixLift 5824224
  have htrace : WordTrace (prefixWord ++ tailWord_5824224) baseStart_5824224 baseEnd_5824224 := by
    simpa [prefixWord, tailWord_5824224, baseEnd_5824224] using wordTrace_append hprefix tailTrace_5824224
  have hstable : (prefixWord ++ tailWord_5824224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824224).length < 2 ^ (prefixWord ++ tailWord_5824224).sum := by decide
  have hdescent : baseEnd_5824224 < baseStart_5824224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824291 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_5824291 : Nat := 118140960795 + 5824291 * 2 ^ 59
def prefixEnd_5824291 : Nat := 4983230072969 + 3 ^ 40 * 5824291 * 2
def baseEnd_5824291 : Nat := 2990660754655777168377079

theorem tailTrace_5824291 : CollatzResearch.WordTrace tailWord_5824291 prefixEnd_5824291 2990660754655777168377079 := by
  unfold tailWord_5824291
  simp only [CollatzResearch.WordTrace]
  refine ⟨212429344542595891555024727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141619563028397261036683151 212429344542595891555024727)
  ·
    refine ⟨318644016813893837332537091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212429344542595891555024727 318644016813893837332537091)
    ·
      refine ⟨477966025220840755998805637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318644016813893837332537091 477966025220840755998805637)
      ·
        refine ⟨89618629728907641749776057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477966025220840755998805637 89618629728907641749776057)
        ·
          refine ⟨67213972296680731312332043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89618629728907641749776057 67213972296680731312332043)
          ·
            refine ⟨100820958445021096968498065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67213972296680731312332043 100820958445021096968498065)
            ·
              refine ⟨75615718833765822726373549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100820958445021096968498065 75615718833765822726373549)
              ·
                refine ⟨28355894562662183522390081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75615718833765822726373549 28355894562662183522390081)
                ·
                  refine ⟨21266920921996637641792561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28355894562662183522390081 21266920921996637641792561)
                  ·
                    refine ⟨15950190691497478231344421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21266920921996637641792561 15950190691497478231344421)
                    ·
                      refine ⟨2990660754655777168377079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15950190691497478231344421 2990660754655777168377079)
                      ·
                        rfl

theorem cell23_5824291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_5824291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824291 prefixEnd_5824291 := by exact prefixLift 5824291
  have htrace : WordTrace (prefixWord ++ tailWord_5824291) baseStart_5824291 baseEnd_5824291 := by
    simpa [prefixWord, tailWord_5824291, baseEnd_5824291] using wordTrace_append hprefix tailTrace_5824291
  have hstable : (prefixWord ++ tailWord_5824291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824291).length < 2 ^ (prefixWord ++ tailWord_5824291).sum := by decide
  have hdescent : baseEnd_5824291 < baseStart_5824291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824311 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_5824311 : Nat := 118140960795 + 5824311 * 2 ^ 59
def prefixEnd_5824311 : Nat := 4983230072969 + 3 ^ 40 * 5824311 * 2
def baseEnd_5824311 : Nat := 2990671024268867090126987

theorem tailTrace_5824311 : CollatzResearch.WordTrace tailWord_5824311 prefixEnd_5824311 2990671024268867090126987 := by
  unfold tailWord_5824311
  simp only [CollatzResearch.WordTrace]
  refine ⟨212430074002523434970752787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141620049335015623313835191 212430074002523434970752787)
  ·
    refine ⟨318645111003785152456129181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212430074002523434970752787 318645111003785152456129181)
    ·
      refine ⟨119491916626419432171048443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318645111003785152456129181 119491916626419432171048443)
      ·
        refine ⟨179237874939629148256572665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119491916626419432171048443 179237874939629148256572665)
        ·
          refine ⟨134428406204721861192429499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179237874939629148256572665 134428406204721861192429499)
          ·
            refine ⟨201642609307082791788644249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134428406204721861192429499 201642609307082791788644249)
            ·
              refine ⟨151231956980312093841483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201642609307082791788644249 151231956980312093841483187)
              ·
                refine ⟨226847935470468140762224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151231956980312093841483187 226847935470468140762224781)
                ·
                  refine ⟨85067975801425552785834293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226847935470468140762224781 85067975801425552785834293)
                  ·
                    refine ⟨7975122731383645573671965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85067975801425552785834293 7975122731383645573671965)
                    ·
                      refine ⟨2990671024268867090126987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7975122731383645573671965 2990671024268867090126987)
                      ·
                        rfl

theorem cell23_5824311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_5824311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824311 prefixEnd_5824311 := by exact prefixLift 5824311
  have htrace : WordTrace (prefixWord ++ tailWord_5824311) baseStart_5824311 baseEnd_5824311 := by
    simpa [prefixWord, tailWord_5824311, baseEnd_5824311] using wordTrace_append hprefix tailTrace_5824311
  have hstable : (prefixWord ++ tailWord_5824311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824311).length < 2 ^ (prefixWord ++ tailWord_5824311).sum := by decide
  have hdescent : baseEnd_5824311 < baseStart_5824311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824368 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2]
def baseStart_5824368 : Nat := 118140960795 + 5824368 * 2 ^ 59
def prefixEnd_5824368 : Nat := 4983230072969 + 3 ^ 40 * 5824368 * 2
def baseEnd_5824368 : Nat := 2990700292666173367114225

theorem tailTrace_5824368 : CollatzResearch.WordTrace tailWord_5824368 prefixEnd_5824368 2990700292666173367114225 := by
  unfold tailWord_5824368
  simp only [CollatzResearch.WordTrace]
  refine ⟨106216076481658466852788879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141621435308877955803718505 106216076481658466852788879)
  ·
    refine ⟨159324114722487700279183319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106216076481658466852788879 159324114722487700279183319)
    ·
      refine ⟨238986172083731550418774979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159324114722487700279183319 238986172083731550418774979)
      ·
        refine ⟨358479258125597325628162469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238986172083731550418774979 358479258125597325628162469)
        ·
          refine ⟨67214860898549498555280463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358479258125597325628162469 67214860898549498555280463)
          ·
            refine ⟨100822291347824247832920695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67214860898549498555280463 100822291347824247832920695)
            ·
              refine ⟨151233437021736371749381043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100822291347824247832920695 151233437021736371749381043)
              ·
                refine ⟨226850155532604557624071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151233437021736371749381043 226850155532604557624071565)
                ·
                  refine ⟨85068808324726709109026837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226850155532604557624071565 85068808324726709109026837)
                  ·
                    refine ⟨3987600390221564489485633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85068808324726709109026837 3987600390221564489485633)
                    ·
                      refine ⟨2990700292666173367114225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987600390221564489485633 2990700292666173367114225)
                      ·
                        rfl

theorem cell23_5824368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2].length) (baseStart_5824368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824368 prefixEnd_5824368 := by exact prefixLift 5824368
  have htrace : WordTrace (prefixWord ++ tailWord_5824368) baseStart_5824368 baseEnd_5824368 := by
    simpa [prefixWord, tailWord_5824368, baseEnd_5824368] using wordTrace_append hprefix tailTrace_5824368
  have hstable : (prefixWord ++ tailWord_5824368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824368).length < 2 ^ (prefixWord ++ tailWord_5824368).sum := by decide
  have hdescent : baseEnd_5824368 < baseStart_5824368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824402 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5824402 : Nat := 118140960795 + 5824402 * 2 ^ 59
def prefixEnd_5824402 : Nat := 4983230072969 + 3 ^ 40 * 5824402 * 2
def baseEnd_5824402 : Nat := 2990717751008426234089069

theorem tailTrace_5824402 : CollatzResearch.WordTrace tailWord_5824402 prefixEnd_5824402 2990717751008426234089069 := by
  unfold tailWord_5824402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108348261298439378078865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141622262030129171674876973 53108348261298439378078865)
  ·
    refine ⟨39831261195973829533559149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53108348261298439378078865 39831261195973829533559149)
    ·
      refine ⟨14936722948490186075084681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39831261195973829533559149 14936722948490186075084681)
      ·
        refine ⟨11202542211367639556313511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14936722948490186075084681 11202542211367639556313511)
        ·
          refine ⟨16803813317051459334470267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202542211367639556313511 16803813317051459334470267)
          ·
            refine ⟨25205719975577189001705401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16803813317051459334470267 25205719975577189001705401)
            ·
              refine ⟨18904289981682891751279051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25205719975577189001705401 18904289981682891751279051)
              ·
                refine ⟨28356434972524337626918577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18904289981682891751279051 28356434972524337626918577)
                ·
                  refine ⟨21267326229393253220188933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28356434972524337626918577 21267326229393253220188933)
                  ·
                    refine ⟨3987623668011234978785425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21267326229393253220188933 3987623668011234978785425)
                    ·
                      refine ⟨2990717751008426234089069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987623668011234978785425 2990717751008426234089069)
                      ·
                        rfl

theorem cell23_5824402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5824402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824402 prefixEnd_5824402 := by exact prefixLift 5824402
  have htrace : WordTrace (prefixWord ++ tailWord_5824402) baseStart_5824402 baseEnd_5824402 := by
    simpa [prefixWord, tailWord_5824402, baseEnd_5824402] using wordTrace_append hprefix tailTrace_5824402
  have hstable : (prefixWord ++ tailWord_5824402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824402).length < 2 ^ (prefixWord ++ tailWord_5824402).sum := by decide
  have hdescent : baseEnd_5824402 < baseStart_5824402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824421 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_5824421 : Nat := 118140960795 + 5824421 * 2 ^ 59
def prefixEnd_5824421 : Nat := 4983230072969 + 3 ^ 40 * 5824421 * 2
def baseEnd_5824421 : Nat := 996909169046953886583827

theorem tailTrace_5824421 : CollatzResearch.WordTrace tailWord_5824421 prefixEnd_5824421 996909169046953886583827 := by
  unfold tailWord_5824421
  simp only [CollatzResearch.WordTrace]
  refine ⟨212434086032124923757257117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141622724021416615838171411 212434086032124923757257117)
  ·
    refine ⟨79662782262046846408971419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212434086032124923757257117 79662782262046846408971419)
    ·
      refine ⟨119494173393070269613457129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79662782262046846408971419 119494173393070269613457129)
      ·
        refine ⟨89620630044802702210092847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119494173393070269613457129 89620630044802702210092847)
        ·
          refine ⟨134430945067204053315139271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89620630044802702210092847 134430945067204053315139271)
          ·
            refine ⟨201646417600806079972708907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134430945067204053315139271 201646417600806079972708907)
            ·
              refine ⟨302469626401209119959063361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201646417600806079972708907 302469626401209119959063361)
              ·
                refine ⟨226852219800906839969297521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302469626401209119959063361 226852219800906839969297521)
                ·
                  refine ⟨170139164850680129976973141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226852219800906839969297521 170139164850680129976973141)
                  ·
                    refine ⟨996909169046953886583827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170139164850680129976973141 996909169046953886583827)
                    ·
                      rfl

theorem cell23_5824421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_5824421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824421 prefixEnd_5824421 := by exact prefixLift 5824421
  have htrace : WordTrace (prefixWord ++ tailWord_5824421) baseStart_5824421 baseEnd_5824421 := by
    simpa [prefixWord, tailWord_5824421, baseEnd_5824421] using wordTrace_append hprefix tailTrace_5824421
  have hstable : (prefixWord ++ tailWord_5824421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824421).length < 2 ^ (prefixWord ++ tailWord_5824421).sum := by decide
  have hdescent : baseEnd_5824421 < baseStart_5824421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824451 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 10]
def baseStart_5824451 : Nat := 118140960795 + 5824451 * 2 ^ 59
def prefixEnd_5824451 : Nat := 4983230072969 + 3 ^ 40 * 5824451 * 2
def baseEnd_5824451 : Nat := 996914303853498847458781

theorem tailTrace_5824451 : CollatzResearch.WordTrace tailWord_5824451 prefixEnd_5824451 996914303853498847458781 := by
  unfold tailWord_5824451
  simp only [CollatzResearch.WordTrace]
  refine ⟨212435180222016238880849207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141623453481344159253899471 212435180222016238880849207)
  ·
    refine ⟨318652770333024358321273811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212435180222016238880849207 318652770333024358321273811)
    ·
      refine ⟨477979155499536537481910717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318652770333024358321273811 477979155499536537481910717)
      ·
        refine ⟨179242183312326201555716519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477979155499536537481910717 179242183312326201555716519)
        ·
          refine ⟨268863274968489302333574779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179242183312326201555716519 268863274968489302333574779)
          ·
            refine ⟨403294912452733953500362169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268863274968489302333574779 403294912452733953500362169)
            ·
              refine ⟨302471184339550465125271627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403294912452733953500362169 302471184339550465125271627)
              ·
                refine ⟨453706776509325697687907441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302471184339550465125271627 453706776509325697687907441)
                ·
                  refine ⟨340280082381994273265930581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453706776509325697687907441 340280082381994273265930581)
                  ·
                    refine ⟨996914303853498847458781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 340280082381994273265930581 996914303853498847458781)
                    ·
                      rfl

theorem cell23_5824451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_5824451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824451 prefixEnd_5824451 := by exact prefixLift 5824451
  have htrace : WordTrace (prefixWord ++ tailWord_5824451) baseStart_5824451 baseEnd_5824451 := by
    simpa [prefixWord, tailWord_5824451, baseEnd_5824451] using wordTrace_append hprefix tailTrace_5824451
  have hstable : (prefixWord ++ tailWord_5824451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824451).length < 2 ^ (prefixWord ++ tailWord_5824451).sum := by decide
  have hdescent : baseEnd_5824451 < baseStart_5824451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824522 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_5824522 : Nat := 118140960795 + 5824522 * 2 ^ 59
def prefixEnd_5824522 : Nat := 4983230072969 + 3 ^ 40 * 5824522 * 2
def baseEnd_5824522 : Nat := 2990779368686965764588517

theorem tailTrace_5824522 : CollatzResearch.WordTrace tailWord_5824522 prefixEnd_5824522 2990779368686965764588517 := by
  unfold tailWord_5824522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53109442451189754501670955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141625179869839345337789213 53109442451189754501670955)
  ·
    refine ⟨79664163676784631752506433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53109442451189754501670955 79664163676784631752506433)
    ·
      refine ⟨59748122757588473814379825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79664163676784631752506433 59748122757588473814379825)
      ·
        refine ⟨44811092068191355360784869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59748122757588473814379825 44811092068191355360784869)
        ·
          refine ⟨8402079762785879130147163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44811092068191355360784869 8402079762785879130147163)
          ·
            refine ⟨12603119644178818695220745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402079762785879130147163 12603119644178818695220745)
            ·
              refine ⟨9452339733134114021415559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12603119644178818695220745 9452339733134114021415559)
              ·
                refine ⟨14178509599701171032123339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9452339733134114021415559 14178509599701171032123339)
                ·
                  refine ⟨21267764399551756548185009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14178509599701171032123339 21267764399551756548185009)
                  ·
                    refine ⟨15950823299663817411138757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21267764399551756548185009 15950823299663817411138757)
                    ·
                      refine ⟨2990779368686965764588517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15950823299663817411138757 2990779368686965764588517)
                      ·
                        rfl

theorem cell23_5824522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_5824522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824522 prefixEnd_5824522 := by exact prefixLift 5824522
  have htrace : WordTrace (prefixWord ++ tailWord_5824522) baseStart_5824522 baseEnd_5824522 := by
    simpa [prefixWord, tailWord_5824522, baseEnd_5824522] using wordTrace_append hprefix tailTrace_5824522
  have hstable : (prefixWord ++ tailWord_5824522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824522).length < 2 ^ (prefixWord ++ tailWord_5824522).sum := by decide
  have hdescent : baseEnd_5824522 < baseStart_5824522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824633 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 2, 2, 2]
def baseStart_5824633 : Nat := 118140960795 + 5824633 * 2 ^ 59
def prefixEnd_5824633 : Nat := 4983230072969 + 3 ^ 40 * 5824633 * 2
def baseEnd_5824633 : Nat := 2990836365039614830300507

theorem tailTrace_5824633 : CollatzResearch.WordTrace tailWord_5824633 prefixEnd_5824633 2990836365039614830300507 := by
  unfold tailWord_5824633
  simp only [CollatzResearch.WordTrace]
  refine ⟨212441818307356883963974553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141627878871571255975983035 212441818307356883963974553)
  ·
    refine ⟨159331363730517662972980915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212441818307356883963974553 159331363730517662972980915)
    ·
      refine ⟨238997045595776494459471373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159331363730517662972980915 238997045595776494459471373)
      ·
        refine ⟨89623892098416185422301765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238997045595776494459471373 89623892098416185422301765)
        ·
          refine ⟨16804479768453034766681581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89623892098416185422301765 16804479768453034766681581)
          ·
            refine ⟨6301679913169888037505593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16804479768453034766681581 6301679913169888037505593)
            ·
              refine ⟨4726259934877416028129195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301679913169888037505593 4726259934877416028129195)
              ·
                refine ⟨7089389902316124042193793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726259934877416028129195 7089389902316124042193793)
                ·
                  refine ⟨5317042426737093031645345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7089389902316124042193793 5317042426737093031645345)
                  ·
                    refine ⟨3987781820052819773734009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5317042426737093031645345 3987781820052819773734009)
                    ·
                      refine ⟨2990836365039614830300507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987781820052819773734009 2990836365039614830300507)
                      ·
                        rfl

theorem cell23_5824633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_5824633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824633 prefixEnd_5824633 := by exact prefixLift 5824633
  have htrace : WordTrace (prefixWord ++ tailWord_5824633) baseStart_5824633 baseEnd_5824633 := by
    simpa [prefixWord, tailWord_5824633, baseEnd_5824633] using wordTrace_append hprefix tailTrace_5824633
  have hstable : (prefixWord ++ tailWord_5824633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824633).length < 2 ^ (prefixWord ++ tailWord_5824633).sum := by decide
  have hdescent : baseEnd_5824633 < baseStart_5824633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824672 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_5824672 : Nat := 118140960795 + 5824672 * 2 ^ 59
def prefixEnd_5824672 : Nat := 4983230072969 + 3 ^ 40 * 5824672 * 2
def baseEnd_5824672 : Nat := 2990856390785140177712827

theorem tailTrace_5824672 : CollatzResearch.WordTrace tailWord_5824672 prefixEnd_5824672 2990856390785140177712827 := by
  unfold tailWord_5824672
  simp only [CollatzResearch.WordTrace]
  refine ⟨106221620377107796812322135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141628827169477062416429513 106221620377107796812322135)
  ·
    refine ⟨159332430565661695218483203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106221620377107796812322135 159332430565661695218483203)
    ·
      refine ⟨238998645848492542827724805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159332430565661695218483203 238998645848492542827724805)
      ·
        refine ⟨44812246096592351780198401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238998645848492542827724805 44812246096592351780198401)
        ·
          refine ⟨33609184572444263835148801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44812246096592351780198401 33609184572444263835148801)
          ·
            refine ⟨25206888429333197876361601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33609184572444263835148801 25206888429333197876361601)
            ·
              refine ⟨18905166321999898407271201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25206888429333197876361601 18905166321999898407271201)
              ·
                refine ⟨14178874741499923805453401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18905166321999898407271201 14178874741499923805453401)
                ·
                  refine ⟨10634156056124942854090051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14178874741499923805453401 10634156056124942854090051)
                  ·
                    refine ⟨15951234084187414281135077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10634156056124942854090051 15951234084187414281135077)
                    ·
                      refine ⟨2990856390785140177712827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15951234084187414281135077 2990856390785140177712827)
                      ·
                        rfl

theorem cell23_5824672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_5824672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824672 prefixEnd_5824672 := by exact prefixLift 5824672
  have htrace : WordTrace (prefixWord ++ tailWord_5824672) baseStart_5824672 baseEnd_5824672 := by
    simpa [prefixWord, tailWord_5824672, baseEnd_5824672] using wordTrace_append hprefix tailTrace_5824672
  have hstable : (prefixWord ++ tailWord_5824672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824672).length < 2 ^ (prefixWord ++ tailWord_5824672).sum := by decide
  have hdescent : baseEnd_5824672 < baseStart_5824672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824675 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3]
def baseStart_5824675 : Nat := 118140960795 + 5824675 * 2 ^ 59
def prefixEnd_5824675 : Nat := 4983230072969 + 3 ^ 40 * 5824675 * 2
def baseEnd_5824675 : Nat := 2990857931227103665975313

theorem tailTrace_5824675 : CollatzResearch.WordTrace tailWord_5824675 prefixEnd_5824675 2990857931227103665975313 := by
  unfold tailWord_5824675
  simp only [CollatzResearch.WordTrace]
  refine ⟨212443350173204725137003479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141628900115469816758002319 212443350173204725137003479)
  ·
    refine ⟨318665025259807087705505219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212443350173204725137003479 318665025259807087705505219)
    ·
      refine ⟨477997537889710631558257829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318665025259807087705505219 477997537889710631558257829)
      ·
        refine ⟨89624538354320743417173343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477997537889710631558257829 89624538354320743417173343)
        ·
          refine ⟨134436807531481115125760015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89624538354320743417173343 134436807531481115125760015)
          ·
            refine ⟨201655211297221672688640023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134436807531481115125760015 201655211297221672688640023)
            ·
              refine ⟨302482816945832509032960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201655211297221672688640023 302482816945832509032960035)
              ·
                refine ⟨453724225418748763549440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302482816945832509032960035 453724225418748763549440053)
                ·
                  refine ⟨42536646133007696582760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 453724225418748763549440053 42536646133007696582760005)
                  ·
                    refine ⟨7975621149938943109267501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42536646133007696582760005 7975621149938943109267501)
                    ·
                      refine ⟨2990857931227103665975313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7975621149938943109267501 2990857931227103665975313)
                      ·
                        rfl

theorem cell23_5824675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_5824675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824675 prefixEnd_5824675 := by exact prefixLift 5824675
  have htrace : WordTrace (prefixWord ++ tailWord_5824675) baseStart_5824675 baseEnd_5824675 := by
    simpa [prefixWord, tailWord_5824675, baseEnd_5824675] using wordTrace_append hprefix tailTrace_5824675
  have hstable : (prefixWord ++ tailWord_5824675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824675).length < 2 ^ (prefixWord ++ tailWord_5824675).sum := by decide
  have hdescent : baseEnd_5824675 < baseStart_5824675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824706 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5824706 : Nat := 118140960795 + 5824706 * 2 ^ 59
def prefixEnd_5824706 : Nat := 4983230072969 + 3 ^ 40 * 5824706 * 2
def baseEnd_5824706 : Nat := 2990873849127393044687671

theorem tailTrace_5824706 : CollatzResearch.WordTrace tailWord_5824706 prefixEnd_5824706 2990873849127393044687671 := by
  unfold tailWord_5824706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53111120209023104357845493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141629653890728278287587981 53111120209023104357845493)
  ·
    refine ⟨4979167519595916033548015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53111120209023104357845493 4979167519595916033548015)
    ·
      refine ⟨7468751279393874050322023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979167519595916033548015 7468751279393874050322023)
      ·
        refine ⟨11203126919090811075483035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468751279393874050322023 11203126919090811075483035)
        ·
          refine ⟨16804690378636216613224553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203126919090811075483035 16804690378636216613224553)
          ·
            refine ⟨12603517783977162459918415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16804690378636216613224553 12603517783977162459918415)
            ·
              refine ⟨18905276675965743689877623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12603517783977162459918415 18905276675965743689877623)
              ·
                refine ⟨28357915013948615534816435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18905276675965743689877623 28357915013948615534816435)
                ·
                  refine ⟨42536872520922923302224653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28357915013948615534816435 42536872520922923302224653)
                  ·
                    refine ⟨15951327195346096238334245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42536872520922923302224653 15951327195346096238334245)
                    ·
                      refine ⟨2990873849127393044687671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15951327195346096238334245 2990873849127393044687671)
                      ·
                        rfl

theorem cell23_5824706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5824706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824706 prefixEnd_5824706 := by exact prefixLift 5824706
  have htrace : WordTrace (prefixWord ++ tailWord_5824706) baseStart_5824706 baseEnd_5824706 := by
    simpa [prefixWord, tailWord_5824706, baseEnd_5824706] using wordTrace_append hprefix tailTrace_5824706
  have hstable : (prefixWord ++ tailWord_5824706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824706).length < 2 ^ (prefixWord ++ tailWord_5824706).sum := by decide
  have hdescent : baseEnd_5824706 < baseStart_5824706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824766 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5824766 : Nat := 118140960795 + 5824766 * 2 ^ 59
def prefixEnd_5824766 : Nat := 4983230072969 + 3 ^ 40 * 5824766 * 2
def baseEnd_5824766 : Nat := 2990904657966662809937395

theorem tailTrace_5824766 : CollatzResearch.WordTrace tailWord_5824766 prefixEnd_5824766 2990904657966662809937395 := by
  unfold tailWord_5824766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26555833651984380959820769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141631112810583365119044101 26555833651984380959820769)
  ·
    refine ⟨19916875238988285719865577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26555833651984380959820769 19916875238988285719865577)
    ·
      refine ⟨14937656429241214289899183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19916875238988285719865577 14937656429241214289899183)
      ·
        refine ⟨22406484643861821434848775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937656429241214289899183 22406484643861821434848775)
        ·
          refine ⟨33609726965792732152273163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22406484643861821434848775 33609726965792732152273163)
          ·
            refine ⟨50414590448689098228409745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33609726965792732152273163 50414590448689098228409745)
            ·
              refine ⟨37810942836516823671307309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50414590448689098228409745 37810942836516823671307309)
              ·
                refine ⟨14179103563693808876740241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37810942836516823671307309 14179103563693808876740241)
                ·
                  refine ⟨10634327672770356657555181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14179103563693808876740241 10634327672770356657555181)
                  ·
                    refine ⟨3987872877288883746583193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10634327672770356657555181 3987872877288883746583193)
                    ·
                      refine ⟨2990904657966662809937395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3987872877288883746583193 2990904657966662809937395)
                      ·
                        rfl

theorem cell23_5824766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5824766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824766 prefixEnd_5824766 := by exact prefixLift 5824766
  have htrace : WordTrace (prefixWord ++ tailWord_5824766) baseStart_5824766 baseEnd_5824766 := by
    simpa [prefixWord, tailWord_5824766, baseEnd_5824766] using wordTrace_append hprefix tailTrace_5824766
  have hstable : (prefixWord ++ tailWord_5824766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824766).length < 2 ^ (prefixWord ++ tailWord_5824766).sum := by decide
  have hdescent : baseEnd_5824766 < baseStart_5824766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824785 : List Nat := [1, 2, 2, 1, 1, 5, 11]
def baseStart_5824785 : Nat := 118140960795 + 5824785 * 2 ^ 59
def prefixEnd_5824785 : Nat := 4983230072969 + 3 ^ 40 * 5824785 * 2
def baseEnd_5824785 : Nat := 36924869309865410316047

theorem tailTrace_5824785 : CollatzResearch.WordTrace tailWord_5824785 prefixEnd_5824785 36924869309865410316047 := by
  unfold tailWord_5824785
  simp only [CollatzResearch.WordTrace]
  refine ⟨212447362202806213923507809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141631574801870809282338539 212447362202806213923507809)
  ·
    refine ⟨159335521652104660442630857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212447362202806213923507809 159335521652104660442630857)
    ·
      refine ⟨119501641239078495331973143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159335521652104660442630857 119501641239078495331973143)
      ·
        refine ⟨179252461858617742997959715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119501641239078495331973143 179252461858617742997959715)
        ·
          refine ⟨268878692787926614496939573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179252461858617742997959715 268878692787926614496939573)
          ·
            refine ⟨25207377448868120109088085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268878692787926614496939573 25207377448868120109088085)
            ·
              refine ⟨36924869309865410316047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25207377448868120109088085 36924869309865410316047)
              ·
                rfl

theorem cell23_5824785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 11].length) (baseStart_5824785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824785 prefixEnd_5824785 := by exact prefixLift 5824785
  have htrace : WordTrace (prefixWord ++ tailWord_5824785) baseStart_5824785 baseEnd_5824785 := by
    simpa [prefixWord, tailWord_5824785, baseEnd_5824785] using wordTrace_append hprefix tailTrace_5824785
  have hstable : (prefixWord ++ tailWord_5824785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824785).length < 2 ^ (prefixWord ++ tailWord_5824785).sum := by decide
  have hdescent : baseEnd_5824785 < baseStart_5824785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824802 : List Nat := [3, 3, 1, 1, 3, 1, 1, 10]
def baseStart_5824802 : Nat := 118140960795 + 5824802 * 2 ^ 59
def prefixEnd_5824802 : Nat := 4983230072969 + 3 ^ 40 * 5824802 * 2
def baseEnd_5824802 : Nat := 110774931232230543299527

theorem tailTrace_5824802 : CollatzResearch.WordTrace tailWord_5824802 prefixEnd_5824802 110774931232230543299527 := by
  unfold tailWord_5824802
  simp only [CollatzResearch.WordTrace]
  refine ⟨53111995560936156456719165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141631988162496417217917773 53111995560936156456719165)
  ·
    refine ⟨19916998335351058671269687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53111995560936156456719165 19916998335351058671269687)
    ·
      refine ⟨29875497503026588006904531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19916998335351058671269687 29875497503026588006904531)
      ·
        refine ⟨44813246254539882010356797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29875497503026588006904531 44813246254539882010356797)
        ·
          refine ⟨16804967345452455753883799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44813246254539882010356797 16804967345452455753883799)
          ·
            refine ⟨25207451018178683630825699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16804967345452455753883799 25207451018178683630825699)
            ·
              refine ⟨37811176527268025446238549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25207451018178683630825699 37811176527268025446238549)
              ·
                refine ⟨110774931232230543299527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37811176527268025446238549 110774931232230543299527)
                ·
                  rfl

theorem cell23_5824802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_5824802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824802 prefixEnd_5824802 := by exact prefixLift 5824802
  have htrace : WordTrace (prefixWord ++ tailWord_5824802) baseStart_5824802 baseEnd_5824802 := by
    simpa [prefixWord, tailWord_5824802, baseEnd_5824802] using wordTrace_append hprefix tailTrace_5824802
  have hstable : (prefixWord ++ tailWord_5824802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824802).length < 2 ^ (prefixWord ++ tailWord_5824802).sum := by decide
  have hdescent : baseEnd_5824802 < baseStart_5824802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824833 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5824833 : Nat := 118140960795 + 5824833 * 2 ^ 59
def prefixEnd_5824833 : Nat := 4983230072969 + 3 ^ 40 * 5824833 * 2
def baseEnd_5824833 : Nat := 2990939061170514047799587

theorem tailTrace_5824833 : CollatzResearch.WordTrace tailWord_5824833 prefixEnd_5824833 2990939061170514047799587 := by
  unfold tailWord_5824833
  simp only [CollatzResearch.WordTrace]
  refine ⟨212449112906632318121255153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141632741937754878747503435 212449112906632318121255153)
  ·
    refine ⟨159336834679974238590941365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212449112906632318121255153 159336834679974238590941365)
    ·
      refine ⟨14937828251247584867900753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159336834679974238590941365 14937828251247584867900753)
      ·
        refine ⟨11203371188435688650925565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14937828251247584867900753 11203371188435688650925565)
        ·
          refine ⟨4201264195663383244097087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11203371188435688650925565 4201264195663383244097087)
          ·
            refine ⟨6301896293495074866145631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201264195663383244097087 6301896293495074866145631)
            ·
              refine ⟨9452844440242612299218447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301896293495074866145631 9452844440242612299218447)
              ·
                refine ⟨14179266660363918448827671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9452844440242612299218447 14179266660363918448827671)
                ·
                  refine ⟨21268899990545877673241507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14179266660363918448827671 21268899990545877673241507)
                  ·
                    refine ⟨31903349985818816509862261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21268899990545877673241507 31903349985818816509862261)
                    ·
                      refine ⟨2990939061170514047799587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31903349985818816509862261 2990939061170514047799587)
                      ·
                        rfl

theorem cell23_5824833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5824833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824833 prefixEnd_5824833 := by exact prefixLift 5824833
  have htrace : WordTrace (prefixWord ++ tailWord_5824833) baseStart_5824833 baseEnd_5824833 := by
    simpa [prefixWord, tailWord_5824833, baseEnd_5824833] using wordTrace_append hprefix tailTrace_5824833
  have hstable : (prefixWord ++ tailWord_5824833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824833).length < 2 ^ (prefixWord ++ tailWord_5824833).sum := by decide
  have hdescent : baseEnd_5824833 < baseStart_5824833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824919 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5824919 : Nat := 118140960795 + 5824919 * 2 ^ 59
def prefixEnd_5824919 : Nat := 4983230072969 + 3 ^ 40 * 5824919 * 2
def baseEnd_5824919 : Nat := 2990983220506800711324191

theorem tailTrace_5824919 : CollatzResearch.WordTrace tailWord_5824919 prefixEnd_5824919 2990983220506800711324191 := by
  unfold tailWord_5824919
  simp only [CollatzResearch.WordTrace]
  refine ⟨212452249584320754808885811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141634833056213836539257207 212452249584320754808885811)
  ·
    refine ⟨318678374376481132213328717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212452249584320754808885811 318678374376481132213328717)
    ·
      refine ⟨119504390391180424579998269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318678374376481132213328717 119504390391180424579998269)
      ·
        refine ⟨44814146396692659217499351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119504390391180424579998269 44814146396692659217499351)
        ·
          refine ⟨67221219595038988826249027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44814146396692659217499351 67221219595038988826249027)
          ·
            refine ⟨100831829392558483239373541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67221219595038988826249027 100831829392558483239373541)
            ·
              refine ⟨18905968011104715607382539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100831829392558483239373541 18905968011104715607382539)
              ·
                refine ⟨28358952016657073411073809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18905968011104715607382539 28358952016657073411073809)
                ·
                  refine ⟨21269214012492805058305357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28358952016657073411073809 21269214012492805058305357)
                  ·
                    refine ⟨7975955254684801896864509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21269214012492805058305357 7975955254684801896864509)
                    ·
                      refine ⟨2990983220506800711324191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7975955254684801896864509 2990983220506800711324191)
                      ·
                        rfl

theorem cell23_5824919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5824919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824919 prefixEnd_5824919 := by exact prefixLift 5824919
  have htrace : WordTrace (prefixWord ++ tailWord_5824919) baseStart_5824919 baseEnd_5824919 := by
    simpa [prefixWord, tailWord_5824919, baseEnd_5824919] using wordTrace_append hprefix tailTrace_5824919
  have hstable : (prefixWord ++ tailWord_5824919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824919).length < 2 ^ (prefixWord ++ tailWord_5824919).sum := by decide
  have hdescent : baseEnd_5824919 < baseStart_5824919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824926 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5824926 : Nat := 118140960795 + 5824926 * 2 ^ 59
def prefixEnd_5824926 : Nat := 4983230072969 + 3 ^ 40 * 5824926 * 2
def baseEnd_5824926 : Nat := 332331868319042464881851

theorem tailTrace_5824926 : CollatzResearch.WordTrace tailWord_5824926 prefixEnd_5824926 332331868319042464881851 := by
  unfold tailWord_5824926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556563111911924375548829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141635003263530263336260421 26556563111911924375548829)
  ·
    refine ⟨9958711166966971640830811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26556563111911924375548829 9958711166966971640830811)
    ·
      refine ⟨14938066750450457461246217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958711166966971640830811 14938066750450457461246217)
      ·
        refine ⟨11203550062837843095934663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14938066750450457461246217 11203550062837843095934663)
        ·
          refine ⟨16805325094256764643901995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203550062837843095934663 16805325094256764643901995)
          ·
            refine ⟨25207987641385146965852993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16805325094256764643901995 25207987641385146965852993)
            ·
              refine ⟨18905990731038860224389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25207987641385146965852993 18905990731038860224389745)
              ·
                refine ⟨14179493048279145168292309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18905990731038860224389745 14179493048279145168292309)
                ·
                  refine ⟨332331868319042464881851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14179493048279145168292309 332331868319042464881851)
                  ·
                    rfl

theorem cell23_5824926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5824926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824926 prefixEnd_5824926 := by exact prefixLift 5824926
  have htrace : WordTrace (prefixWord ++ tailWord_5824926) baseStart_5824926 baseEnd_5824926 := by
    simpa [prefixWord, tailWord_5824926, baseEnd_5824926] using wordTrace_append hprefix tailTrace_5824926
  have hstable : (prefixWord ++ tailWord_5824926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824926).length < 2 ^ (prefixWord ++ tailWord_5824926).sum := by decide
  have hdescent : baseEnd_5824926 < baseStart_5824926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5824956 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_5824956 : Nat := 118140960795 + 5824956 * 2 ^ 59
def prefixEnd_5824956 : Nat := 4983230072969 + 3 ^ 40 * 5824956 * 2
def baseEnd_5824956 : Nat := 997000739763672355520507

theorem tailTrace_5824956 : CollatzResearch.WordTrace tailWord_5824956 prefixEnd_5824956 997000739763672355520507 := by
  unfold tailWord_5824956
  simp only [CollatzResearch.WordTrace]
  refine ⟨106226799542593355063991361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141635732723457806751988481 106226799542593355063991361)
  ·
    refine ⟨79670099656945016297993521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106226799542593355063991361 79670099656945016297993521)
    ·
      refine ⟨59752574742708762223495141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79670099656945016297993521 59752574742708762223495141)
      ·
        refine ⟨11203607764257892916905339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59752574742708762223495141 11203607764257892916905339)
        ·
          refine ⟨16805411646386839375358009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203607764257892916905339 16805411646386839375358009)
          ·
            refine ⟨12604058734790129531518507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16805411646386839375358009 12604058734790129531518507)
            ·
              refine ⟨18906088102185194297277761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12604058734790129531518507 18906088102185194297277761)
              ·
                refine ⟨14179566076638895722958321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18906088102185194297277761 14179566076638895722958321)
                ·
                  refine ⟨10634674557479171792218741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14179566076638895722958321 10634674557479171792218741)
                  ·
                    refine ⟨997000739763672355520507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10634674557479171792218741 997000739763672355520507)
                    ·
                      rfl

theorem cell23_5824956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_5824956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5824956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5824956 prefixEnd_5824956 := by exact prefixLift 5824956
  have htrace : WordTrace (prefixWord ++ tailWord_5824956) baseStart_5824956 baseEnd_5824956 := by
    simpa [prefixWord, tailWord_5824956, baseEnd_5824956] using wordTrace_append hprefix tailTrace_5824956
  have hstable : (prefixWord ++ tailWord_5824956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5824956).length < 2 ^ (prefixWord ++ tailWord_5824956).sum := by decide
  have hdescent : baseEnd_5824956 < baseStart_5824956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5824956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825029 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_5825029 : Nat := 118140960795 + 5825029 * 2 ^ 59
def prefixEnd_5825029 : Nat := 4983230072969 + 3 ^ 40 * 5825029 * 2
def baseEnd_5825029 : Nat := 997013234459598426982895

theorem tailTrace_5825029 : CollatzResearch.WordTrace tailWord_5825029 prefixEnd_5825029 997013234459598426982895 := by
  unfold tailWord_5825029
  simp only [CollatzResearch.WordTrace]
  refine ⟨212456261613922243595390141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141637507742614829063593427 212456261613922243595390141)
  ·
    refine ⟨79671098105220841348271303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212456261613922243595390141 79671098105220841348271303)
    ·
      refine ⟨119506647157831262022406955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79671098105220841348271303 119506647157831262022406955)
      ·
        refine ⟨179259970736746893033610433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119506647157831262022406955 179259970736746893033610433)
        ·
          refine ⟨134444978052560169775207825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179259970736746893033610433 134444978052560169775207825)
          ·
            refine ⟨100833733539420127331405869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134444978052560169775207825 100833733539420127331405869)
            ·
              refine ⟨37812650077282547749277201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100833733539420127331405869 37812650077282547749277201)
              ·
                refine ⟨28359487557961910811957901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37812650077282547749277201 28359487557961910811957901)
                ·
                  refine ⟨10634807834235716554484213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28359487557961910811957901 10634807834235716554484213)
                  ·
                    refine ⟨997013234459598426982895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10634807834235716554484213 997013234459598426982895)
                    ·
                      rfl

theorem cell23_5825029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_5825029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825029 prefixEnd_5825029 := by exact prefixLift 5825029
  have htrace : WordTrace (prefixWord ++ tailWord_5825029) baseStart_5825029 baseEnd_5825029 := by
    simpa [prefixWord, tailWord_5825029, baseEnd_5825029] using wordTrace_append hprefix tailTrace_5825029
  have hstable : (prefixWord ++ tailWord_5825029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825029).length < 2 ^ (prefixWord ++ tailWord_5825029).sum := by decide
  have hdescent : baseEnd_5825029 < baseStart_5825029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825047 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5825047 : Nat := 118140960795 + 5825047 * 2 ^ 59
def prefixEnd_5825047 : Nat := 4983230072969 + 3 ^ 40 * 5825047 * 2
def baseEnd_5825047 : Nat := 2991048946030576210523603

theorem tailTrace_5825047 : CollatzResearch.WordTrace tailWord_5825047 prefixEnd_5825047 2991048946030576210523603 := by
  unfold tailWord_5825047
  simp only [CollatzResearch.WordTrace]
  refine ⟨212456918127857032669545395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141637945418571355113030263 212456918127857032669545395)
  ·
    refine ⟨318685377191785549004318093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212456918127857032669545395 318685377191785549004318093)
    ·
      refine ⟨119507016446919580876619285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318685377191785549004318093 119507016446919580876619285)
      ·
        refine ⟨5601891395949355353591529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119507016446919580876619285 5601891395949355353591529)
        ·
          refine ⟨4201418546962016515193647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601891395949355353591529 4201418546962016515193647)
          ·
            refine ⟨6302127820443024772790471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201418546962016515193647 6302127820443024772790471)
            ·
              refine ⟨9453191730664537159185707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302127820443024772790471 9453191730664537159185707)
              ·
                refine ⟨14179787595996805738778561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453191730664537159185707 14179787595996805738778561)
                ·
                  refine ⟨10634840696997604304083921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14179787595996805738778561 10634840696997604304083921)
                  ·
                    refine ⟨7976130522748203228062941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10634840696997604304083921 7976130522748203228062941)
                    ·
                      refine ⟨2991048946030576210523603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976130522748203228062941 2991048946030576210523603)
                      ·
                        rfl

theorem cell23_5825047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5825047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825047 prefixEnd_5825047 := by exact prefixLift 5825047
  have htrace : WordTrace (prefixWord ++ tailWord_5825047) baseStart_5825047 baseEnd_5825047 := by
    simpa [prefixWord, tailWord_5825047, baseEnd_5825047] using wordTrace_append hprefix tailTrace_5825047
  have hstable : (prefixWord ++ tailWord_5825047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825047).length < 2 ^ (prefixWord ++ tailWord_5825047).sum := by decide
  have hdescent : baseEnd_5825047 < baseStart_5825047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825053 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5825053 : Nat := 118140960795 + 5825053 * 2 ^ 59
def prefixEnd_5825053 : Nat := 4983230072969 + 3 ^ 40 * 5825053 * 2
def baseEnd_5825053 : Nat := 2991052026914503187048575

theorem tailTrace_5825053 : CollatzResearch.WordTrace tailWord_5825053 prefixEnd_5825053 2991052026914503187048575 := by
  unfold tailWord_5825053
  simp only [CollatzResearch.WordTrace]
  refine ⟨212457136965835295694263813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141638091310556863796175875 212457136965835295694263813)
  ·
    refine ⟨39835713181094117942674465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 212457136965835295694263813 39835713181094117942674465)
    ·
      refine ⟨29876784885820588457005849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39835713181094117942674465 29876784885820588457005849)
      ·
        refine ⟨22407588664365441342754387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29876784885820588457005849 22407588664365441342754387)
        ·
          refine ⟨33611382996548162014131581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407588664365441342754387 33611382996548162014131581)
          ·
            refine ⟨12604268623705560755299343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33611382996548162014131581 12604268623705560755299343)
            ·
              refine ⟨18906402935558341132949015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12604268623705560755299343 18906402935558341132949015)
              ·
                refine ⟨28359604403337511699423523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18906402935558341132949015 28359604403337511699423523)
                ·
                  refine ⟨42539406605006267549135285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28359604403337511699423523 42539406605006267549135285)
                  ·
                    refine ⟨3988069369219337582731433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42539406605006267549135285 3988069369219337582731433)
                    ·
                      refine ⟨2991052026914503187048575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3988069369219337582731433 2991052026914503187048575)
                      ·
                        rfl

theorem cell23_5825053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5825053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825053 prefixEnd_5825053 := by exact prefixLift 5825053
  have htrace : WordTrace (prefixWord ++ tailWord_5825053) baseStart_5825053 baseEnd_5825053 := by
    simpa [prefixWord, tailWord_5825053, baseEnd_5825053] using wordTrace_append hprefix tailTrace_5825053
  have hstable : (prefixWord ++ tailWord_5825053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825053).length < 2 ^ (prefixWord ++ tailWord_5825053).sum := by decide
  have hdescent : baseEnd_5825053 < baseStart_5825053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825079 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_5825079 : Nat := 118140960795 + 5825079 * 2 ^ 59
def prefixEnd_5825079 : Nat := 4983230072969 + 3 ^ 40 * 5825079 * 2
def baseEnd_5825079 : Nat := 2991065377411520085323455

theorem tailTrace_5825079 : CollatzResearch.WordTrace tailWord_5825079 prefixEnd_5825079 2991065377411520085323455 := by
  unfold tailWord_5825079
  simp only [CollatzResearch.WordTrace]
  refine ⟨212458085263741102134710291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141638723509160734756473527 212458085263741102134710291)
  ·
    refine ⟨318687127895611653202065437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212458085263741102134710291 318687127895611653202065437)
    ·
      refine ⟨119507672960854369950774539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318687127895611653202065437 119507672960854369950774539)
      ·
        refine ⟨179261509441281554926161809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119507672960854369950774539 179261509441281554926161809)
        ·
          refine ⟨134446132080961166194621357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179261509441281554926161809 134446132080961166194621357)
          ·
            refine ⟨50417299530360437322983009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134446132080961166194621357 50417299530360437322983009)
            ·
              refine ⟨37812974647770327992237257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50417299530360437322983009 37812974647770327992237257)
              ·
                refine ⟨28359730985827745994177943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37812974647770327992237257 28359730985827745994177943)
                ·
                  refine ⟨42539596478741618991266915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28359730985827745994177943 42539596478741618991266915)
                  ·
                    refine ⟨63809394718112428486900373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42539596478741618991266915 63809394718112428486900373)
                    ·
                      refine ⟨2991065377411520085323455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63809394718112428486900373 2991065377411520085323455)
                      ·
                        rfl

theorem cell23_5825079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_5825079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825079 prefixEnd_5825079 := by exact prefixLift 5825079
  have htrace : WordTrace (prefixWord ++ tailWord_5825079) baseStart_5825079 baseEnd_5825079 := by
    simpa [prefixWord, tailWord_5825079, baseEnd_5825079] using wordTrace_append hprefix tailTrace_5825079
  have hstable : (prefixWord ++ tailWord_5825079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825079).length < 2 ^ (prefixWord ++ tailWord_5825079).sum := by decide
  have hdescent : baseEnd_5825079 < baseStart_5825079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825129 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_5825129 : Nat := 118140960795 + 5825129 * 2 ^ 59
def prefixEnd_5825129 : Nat := 4983230072969 + 3 ^ 40 * 5825129 * 2
def baseEnd_5825129 : Nat := 2991091051444244889698225

theorem tailTrace_5825129 : CollatzResearch.WordTrace tailWord_5825129 prefixEnd_5825129 2991091051444244889698225 := by
  unfold tailWord_5825129
  simp only [CollatzResearch.WordTrace]
  refine ⟨212459908913559960674030441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141639939275706640449353627 212459908913559960674030441)
  ·
    refine ⟨159344931685169970505522831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212459908913559960674030441 159344931685169970505522831)
    ·
      refine ⟨239017397527754955758284247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159344931685169970505522831 239017397527754955758284247)
      ·
        refine ⟨358526096291632433637426371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239017397527754955758284247 358526096291632433637426371)
        ·
          refine ⟨537789144437448650456139557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358526096291632433637426371 537789144437448650456139557)
          ·
            refine ⟨100835464582021621960526167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 537789144437448650456139557 100835464582021621960526167)
            ·
              refine ⟨151253196873032432940789251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100835464582021621960526167 151253196873032432940789251)
              ·
                refine ⟨226879795309548649411183877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151253196873032432940789251 226879795309548649411183877)
                ·
                  refine ⟨42539961620540371764596977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226879795309548649411183877 42539961620540371764596977)
                  ·
                    refine ⟨31904971215405278823447733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42539961620540371764596977 31904971215405278823447733)
                    ·
                      refine ⟨2991091051444244889698225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31904971215405278823447733 2991091051444244889698225)
                      ·
                        rfl

theorem cell23_5825129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_5825129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825129 prefixEnd_5825129 := by exact prefixLift 5825129
  have htrace : WordTrace (prefixWord ++ tailWord_5825129) baseStart_5825129 baseEnd_5825129 := by
    simpa [prefixWord, tailWord_5825129, baseEnd_5825129] using wordTrace_append hprefix tailTrace_5825129
  have hstable : (prefixWord ++ tailWord_5825129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825129).length < 2 ^ (prefixWord ++ tailWord_5825129).sum := by decide
  have hdescent : baseEnd_5825129 < baseStart_5825129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825154 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5825154 : Nat := 118140960795 + 5825154 * 2 ^ 59
def prefixEnd_5825154 : Nat := 4983230072969 + 3 ^ 40 * 5825154 * 2
def baseEnd_5825154 : Nat := 2991103888460607291885611

theorem tailTrace_5825154 : CollatzResearch.WordTrace tailWord_5825154 prefixEnd_5825154 2991103888460607291885611 := by
  unfold tailWord_5825154
  simp only [CollatzResearch.WordTrace]
  refine ⟨53115205184617347485922629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141640547158979593295793677 53115205184617347485922629)
  ·
    refine ⟨9959100972115752653610493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53115205184617347485922629 9959100972115752653610493)
    ·
      refine ⟨3734662864543407245103935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9959100972115752653610493 3734662864543407245103935)
      ·
        refine ⟨5601994296815110867655903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734662864543407245103935 5601994296815110867655903)
        ·
          refine ⟨8402991445222666301483855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601994296815110867655903 8402991445222666301483855)
          ·
            refine ⟨12604487167833999452225783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402991445222666301483855 12604487167833999452225783)
            ·
              refine ⟨18906730751750999178338675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12604487167833999452225783 18906730751750999178338675)
              ·
                refine ⟨28360096127626498767508013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18906730751750999178338675 28360096127626498767508013)
                ·
                  refine ⟨10635036047859937037815505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28360096127626498767508013 10635036047859937037815505)
                  ·
                    refine ⟨7976277035894952778361629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635036047859937037815505 7976277035894952778361629)
                    ·
                      refine ⟨2991103888460607291885611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976277035894952778361629 2991103888460607291885611)
                      ·
                        rfl

theorem cell23_5825154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5825154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825154 prefixEnd_5825154 := by exact prefixLift 5825154
  have htrace : WordTrace (prefixWord ++ tailWord_5825154) baseStart_5825154 baseEnd_5825154 := by
    simpa [prefixWord, tailWord_5825154, baseEnd_5825154] using wordTrace_append hprefix tailTrace_5825154
  have hstable : (prefixWord ++ tailWord_5825154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825154).length < 2 ^ (prefixWord ++ tailWord_5825154).sum := by decide
  have hdescent : baseEnd_5825154 < baseStart_5825154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_5825169 : Nat := 118140960795 + 5825169 * 2 ^ 59
def prefixEnd_5825169 : Nat := 4983230072969 + 3 ^ 40 * 5825169 * 2
def baseEnd_5825169 : Nat := 2991111590670424733198041

theorem tailTrace_5825169 : CollatzResearch.WordTrace tailWord_5825169 prefixEnd_5825169 2991111590670424733198041 := by
  unfold tailWord_5825169
  simp only [CollatzResearch.WordTrace]
  refine ⟨212461367833415047505486561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141640911888943365003657707 212461367833415047505486561)
  ·
    refine ⟨159346025875061285629114921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212461367833415047505486561 159346025875061285629114921)
    ·
      refine ⟨119509519406295964221836191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159346025875061285629114921 119509519406295964221836191)
      ·
        refine ⟨179264279109443946332754287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119509519406295964221836191 179264279109443946332754287)
        ·
          refine ⟨268896418664165919499131431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179264279109443946332754287 268896418664165919499131431)
          ·
            refine ⟨403344627996248879248697147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268896418664165919499131431 403344627996248879248697147)
            ·
              refine ⟨605016941994373318873045721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403344627996248879248697147 605016941994373318873045721)
              ·
                refine ⟨453762706495779989154784291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605016941994373318873045721 453762706495779989154784291)
                ·
                  refine ⟨680644059743669983732176437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453762706495779989154784291 680644059743669983732176437)
                  ·
                    refine ⟨63810380600969060974891541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 680644059743669983732176437 63810380600969060974891541)
                    ·
                      refine ⟨2991111590670424733198041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63810380600969060974891541 2991111590670424733198041)
                      ·
                        rfl

theorem cell23_5825169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_5825169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825169 prefixEnd_5825169 := by exact prefixLift 5825169
  have htrace : WordTrace (prefixWord ++ tailWord_5825169) baseStart_5825169 baseEnd_5825169 := by
    simpa [prefixWord, tailWord_5825169, baseEnd_5825169] using wordTrace_append hprefix tailTrace_5825169
  have hstable : (prefixWord ++ tailWord_5825169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825169).length < 2 ^ (prefixWord ++ tailWord_5825169).sum := by decide
  have hdescent : baseEnd_5825169 < baseStart_5825169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825176 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5825176 : Nat := 118140960795 + 5825176 * 2 ^ 59
def prefixEnd_5825176 : Nat := 4983230072969 + 3 ^ 40 * 5825176 * 2
def baseEnd_5825176 : Nat := 2991115185035006205810509

theorem tailTrace_5825176 : CollatzResearch.WordTrace tailWord_5825176 prefixEnd_5825176 2991115185035006205810509 := by
  unfold tailWord_5825176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106230811572194843850495691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141641082096259791800660921 106230811572194843850495691)
  ·
    refine ⟨159346217358292265775743537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106230811572194843850495691 159346217358292265775743537)
    ·
      refine ⟨119509663018719199331807653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159346217358292265775743537 119509663018719199331807653)
      ·
        refine ⟨22408061816009849874713935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119509663018719199331807653 22408061816009849874713935)
        ·
          refine ⟨33612092724014774812070903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22408061816009849874713935 33612092724014774812070903)
          ·
            refine ⟨50418139086022162218106355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33612092724014774812070903 50418139086022162218106355)
            ·
              refine ⟨75627208629033243327159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50418139086022162218106355 75627208629033243327159533)
              ·
                refine ⟨28360203235887466247684825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75627208629033243327159533 28360203235887466247684825)
                ·
                  refine ⟨21270152426915599685763619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28360203235887466247684825 21270152426915599685763619)
                  ·
                    refine ⟨31905228640373399528645429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21270152426915599685763619 31905228640373399528645429)
                    ·
                      refine ⟨2991115185035006205810509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31905228640373399528645429 2991115185035006205810509)
                      ·
                        rfl

theorem cell23_5825176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5825176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825176 prefixEnd_5825176 := by exact prefixLift 5825176
  have htrace : WordTrace (prefixWord ++ tailWord_5825176) baseStart_5825176 baseEnd_5825176 := by
    simpa [prefixWord, tailWord_5825176, baseEnd_5825176] using wordTrace_append hprefix tailTrace_5825176
  have hstable : (prefixWord ++ tailWord_5825176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825176).length < 2 ^ (prefixWord ++ tailWord_5825176).sum := by decide
  have hdescent : baseEnd_5825176 < baseStart_5825176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825230 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_5825230 : Nat := 118140960795 + 5825230 * 2 ^ 59
def prefixEnd_5825230 : Nat := 4983230072969 + 3 ^ 40 * 5825230 * 2
def baseEnd_5825230 : Nat := 332349212554483221615029

theorem tailTrace_5825230 : CollatzResearch.WordTrace tailWord_5825230 prefixEnd_5825230 332349212554483221615029 := by
  unfold tailWord_5825230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26557949085774256865432143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141642395124129369948971429 26557949085774256865432143)
  ·
    refine ⟨39836923628661385298148215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26557949085774256865432143 39836923628661385298148215)
    ·
      refine ⟨59755385442992077947222323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39836923628661385298148215 59755385442992077947222323)
      ·
        refine ⟨89633078164488116920833485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59755385442992077947222323 89633078164488116920833485)
        ·
          refine ⟨33612404311683043845312557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89633078164488116920833485 33612404311683043845312557)
          ·
            refine ⟨12604651616881141441992209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33612404311683043845312557 12604651616881141441992209)
            ·
              refine ⟨9453488712660856081494157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12604651616881141441992209 9453488712660856081494157)
              ·
                refine ⟨3545058267247821030560309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9453488712660856081494157 3545058267247821030560309)
                ·
                  refine ⟨332349212554483221615029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3545058267247821030560309 332349212554483221615029)
                  ·
                    rfl

theorem cell23_5825230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_5825230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825230 prefixEnd_5825230 := by exact prefixLift 5825230
  have htrace : WordTrace (prefixWord ++ tailWord_5825230) baseStart_5825230 baseEnd_5825230 := by
    simpa [prefixWord, tailWord_5825230, baseEnd_5825230] using wordTrace_append hprefix tailTrace_5825230
  have hstable : (prefixWord ++ tailWord_5825230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825230).length < 2 ^ (prefixWord ++ tailWord_5825230).sum := by decide
  have hdescent : baseEnd_5825230 < baseStart_5825230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825283 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3]
def baseStart_5825283 : Nat := 118140960795 + 5825283 * 2 ^ 59
def prefixEnd_5825283 : Nat := 4983230072969 + 3 ^ 40 * 5825283 * 2
def baseEnd_5825283 : Nat := 2991170127465037287172517

theorem tailTrace_5825283 : CollatzResearch.WordTrace tailWord_5825283 prefixEnd_5825283 2991170127465037287172517 := by
  unfold tailWord_5825283
  simp only [CollatzResearch.WordTrace]
  refine ⟨212465525755002044975136503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141643683836668029983424335 212465525755002044975136503)
  ·
    refine ⟨318698288632503067462704755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212465525755002044975136503 318698288632503067462704755)
    ·
      refine ⟨478047432948754601194057133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318698288632503067462704755 478047432948754601194057133)
      ·
        refine ⟨179267787355782975447771425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478047432948754601194057133 179267787355782975447771425)
        ·
          refine ⟨134450840516837231585828569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179267787355782975447771425 134450840516837231585828569)
          ·
            refine ⟨100838130387627923689371427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134450840516837231585828569 100838130387627923689371427)
            ·
              refine ⟨151257195581441885534057141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100838130387627923689371427 151257195581441885534057141)
              ·
                refine ⟨14180362085760176768817857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151257195581441885534057141 14180362085760176768817857)
                ·
                  refine ⟨10635271564320132576613393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14180362085760176768817857 10635271564320132576613393)
                  ·
                    refine ⟨7976453673240099432460045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635271564320132576613393 7976453673240099432460045)
                    ·
                      refine ⟨2991170127465037287172517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976453673240099432460045 2991170127465037287172517)
                      ·
                        rfl

theorem cell23_5825283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_5825283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825283 prefixEnd_5825283 := by exact prefixLift 5825283
  have htrace : WordTrace (prefixWord ++ tailWord_5825283) baseStart_5825283 baseEnd_5825283 := by
    simpa [prefixWord, tailWord_5825283, baseEnd_5825283] using wordTrace_append hprefix tailTrace_5825283
  have hstable : (prefixWord ++ tailWord_5825283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825283).length < 2 ^ (prefixWord ++ tailWord_5825283).sum := by decide
  have hdescent : baseEnd_5825283 < baseStart_5825283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825330 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_5825330 : Nat := 118140960795 + 5825330 * 2 ^ 59
def prefixEnd_5825330 : Nat := 4983230072969 + 3 ^ 40 * 5825330 * 2
def baseEnd_5825330 : Nat := 2991194261055798603284801

theorem tailTrace_5825330 : CollatzResearch.WordTrace tailWord_5825330 prefixEnd_5825330 2991194261055798603284801 := by
  unfold tailWord_5825330
  simp only [CollatzResearch.WordTrace]
  refine ⟨53116809996457943000524361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141644826657221181334731629 53116809996457943000524361)
  ·
    refine ⟨39837607497343457250393271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53116809996457943000524361 39837607497343457250393271)
    ·
      refine ⟨59756411246015185875589907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39837607497343457250393271 59756411246015185875589907)
      ·
        refine ⟨89634616869022778813384861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59756411246015185875589907 89634616869022778813384861)
        ·
          refine ⟨33612981325883542055019323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89634616869022778813384861 33612981325883542055019323)
          ·
            refine ⟨50419471988825313082528985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33612981325883542055019323 50419471988825313082528985)
            ·
              refine ⟨37814603991618984811896739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50419471988825313082528985 37814603991618984811896739)
              ·
                refine ⟨56721905987428477217845109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37814603991618984811896739 56721905987428477217845109)
                ·
                  refine ⟨5317678686321419739172979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56721905987428477217845109 5317678686321419739172979)
                  ·
                    refine ⟨7976518029482129608759469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5317678686321419739172979 7976518029482129608759469)
                    ·
                      refine ⟨2991194261055798603284801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976518029482129608759469 2991194261055798603284801)
                      ·
                        rfl

theorem cell23_5825330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_5825330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825330 prefixEnd_5825330 := by exact prefixLift 5825330
  have htrace : WordTrace (prefixWord ++ tailWord_5825330) baseStart_5825330 baseEnd_5825330 := by
    simpa [prefixWord, tailWord_5825330, baseEnd_5825330] using wordTrace_append hprefix tailTrace_5825330
  have hstable : (prefixWord ++ tailWord_5825330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825330).length < 2 ^ (prefixWord ++ tailWord_5825330).sum := by decide
  have hdescent : baseEnd_5825330 < baseStart_5825330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825334 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5825334 : Nat := 118140960795 + 5825334 * 2 ^ 59
def prefixEnd_5825334 : Nat := 4983230072969 + 3 ^ 40 * 5825334 * 2
def baseEnd_5825334 : Nat := 2991196314978416587634783

theorem tailTrace_5825334 : CollatzResearch.WordTrace tailWord_5825334 prefixEnd_5825334 2991196314978416587634783 := by
  unfold tailWord_5825334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279211617363580042827691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141644923918544853790162037 13279211617363580042827691)
  ·
    refine ⟨19918817426045370064241537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13279211617363580042827691 19918817426045370064241537)
    ·
      refine ⟨14939113069534027548181153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19918817426045370064241537 14939113069534027548181153)
      ·
        refine ⟨11204334802150520661135865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14939113069534027548181153 11204334802150520661135865)
        ·
          refine ⟨8403251101612890495851899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11204334802150520661135865 8403251101612890495851899)
          ·
            refine ⟨12604876652419335743777849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8403251101612890495851899 12604876652419335743777849)
            ·
              refine ⟨9453657489314501807833387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12604876652419335743777849 9453657489314501807833387)
              ·
                refine ⟨14180486233971752711750081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453657489314501807833387 14180486233971752711750081)
                ·
                  refine ⟨10635364675478814533812561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14180486233971752711750081 10635364675478814533812561)
                  ·
                    refine ⟨7976523506609110900359421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10635364675478814533812561 7976523506609110900359421)
                    ·
                      refine ⟨2991196314978416587634783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976523506609110900359421 2991196314978416587634783)
                      ·
                        rfl

theorem cell23_5825334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5825334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825334 prefixEnd_5825334 := by exact prefixLift 5825334
  have htrace : WordTrace (prefixWord ++ tailWord_5825334) baseStart_5825334 baseEnd_5825334 := by
    simpa [prefixWord, tailWord_5825334, baseEnd_5825334] using wordTrace_append hprefix tailTrace_5825334
  have hstable : (prefixWord ++ tailWord_5825334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825334).length < 2 ^ (prefixWord ++ tailWord_5825334).sum := by decide
  have hdescent : baseEnd_5825334 < baseStart_5825334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825347 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 1, 1, 3]
def baseStart_5825347 : Nat := 118140960795 + 5825347 * 2 ^ 59
def prefixEnd_5825347 : Nat := 4983230072969 + 3 ^ 40 * 5825347 * 2
def baseEnd_5825347 : Nat := 2991202990226925036772223

theorem tailTrace_5825347 : CollatzResearch.WordTrace tailWord_5825347 prefixEnd_5825347 2991202990226925036772223 := by
  unfold tailWord_5825347
  simp only [CollatzResearch.WordTrace]
  refine ⟨212467860026770183905466295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141645240017846789270310863 212467860026770183905466295)
  ·
    refine ⟨318701790040155275858199443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212467860026770183905466295 318701790040155275858199443)
    ·
      refine ⟨478052685060232913787299165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318701790040155275858199443 478052685060232913787299165)
      ·
        refine ⟨179269756897587342670237187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478052685060232913787299165 179269756897587342670237187)
        ·
          refine ⟨268904635346381014005355781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179269756897587342670237187 268904635346381014005355781)
          ·
            refine ⟨50419619127446440126004209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268904635346381014005355781 50419619127446440126004209)
            ·
              refine ⟨37814714345584830094503157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50419619127446440126004209 37814714345584830094503157)
              ·
                refine ⟨3545129469898577821359671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37814714345584830094503157 3545129469898577821359671)
                ·
                  refine ⟨5317694204847866732039507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545129469898577821359671 5317694204847866732039507)
                  ·
                    refine ⟨7976541307271800098059261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5317694204847866732039507 7976541307271800098059261)
                    ·
                      refine ⟨2991202990226925036772223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7976541307271800098059261 2991202990226925036772223)
                      ·
                        rfl

theorem cell23_5825347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_5825347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825347 prefixEnd_5825347 := by exact prefixLift 5825347
  have htrace : WordTrace (prefixWord ++ tailWord_5825347) baseStart_5825347 baseEnd_5825347 := by
    simpa [prefixWord, tailWord_5825347, baseEnd_5825347] using wordTrace_append hprefix tailTrace_5825347
  have hstable : (prefixWord ++ tailWord_5825347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825347).length < 2 ^ (prefixWord ++ tailWord_5825347).sum := by decide
  have hdescent : baseEnd_5825347 < baseStart_5825347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825363 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 4, 4]
def baseStart_5825363 : Nat := 118140960795 + 5825363 * 2 ^ 59
def prefixEnd_5825363 : Nat := 4983230072969 + 3 ^ 40 * 5825363 * 2
def baseEnd_5825363 : Nat := 997070401972465658057383

theorem tailTrace_5825363 : CollatzResearch.WordTrace tailWord_5825363 prefixEnd_5825363 997070401972465658057383 := by
  unfold tailWord_5825363
  simp only [CollatzResearch.WordTrace]
  refine ⟨212468443594712218638048743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141645629063141479092032495 212468443594712218638048743)
  ·
    refine ⟨318702665392068327957073115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212468443594712218638048743 318702665392068327957073115)
    ·
      refine ⟨478053998088102491935609673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318702665392068327957073115 478053998088102491935609673)
      ·
        refine ⟨358540498566076868951707255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478053998088102491935609673 358540498566076868951707255)
        ·
          refine ⟨537810747849115303427560883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358540498566076868951707255 537810747849115303427560883)
          ·
            refine ⟨806716121773672955141341325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537810747849115303427560883 806716121773672955141341325)
            ·
              refine ⟨302518545665127358178002997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 806716121773672955141341325 302518545665127358178002997)
              ·
                refine ⟨28361113656105689829187781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302518545665127358178002997 28361113656105689829187781)
                ·
                  refine ⟨5317708810519816842972709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28361113656105689829187781 5317708810519816842972709)
                  ·
                    refine ⟨997070401972465658057383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317708810519816842972709 997070401972465658057383)
                    ·
                      rfl

theorem cell23_5825363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 4].length) (baseStart_5825363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825363 prefixEnd_5825363 := by exact prefixLift 5825363
  have htrace : WordTrace (prefixWord ++ tailWord_5825363) baseStart_5825363 baseEnd_5825363 := by
    simpa [prefixWord, tailWord_5825363, baseEnd_5825363] using wordTrace_append hprefix tailTrace_5825363
  have hstable : (prefixWord ++ tailWord_5825363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825363).length < 2 ^ (prefixWord ++ tailWord_5825363).sum := by decide
  have hdescent : baseEnd_5825363 < baseStart_5825363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5825380 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_5825380 : Nat := 118140960795 + 5825380 * 2 ^ 59
def prefixEnd_5825380 : Nat := 4983230072969 + 3 ^ 40 * 5825380 * 2
def baseEnd_5825380 : Nat := 997073311696174469219857

theorem tailTrace_5825380 : CollatzResearch.WordTrace tailWord_5825380 prefixEnd_5825380 997073311696174469219857 := by
  unfold tailWord_5825380
  simp only [CollatzResearch.WordTrace]
  refine ⟨106234531817825315270708797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141646042423767087027611729 106234531817825315270708797)
  ·
    refine ⟨39837949431684493226515799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106234531817825315270708797 39837949431684493226515799)
    ·
      refine ⟨59756924147526739839773699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39837949431684493226515799 59756924147526739839773699)
      ·
        refine ⟨89635386221290109759660549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59756924147526739839773699 89635386221290109759660549)
        ·
          refine ⟨16806634916491895579936353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89635386221290109759660549 16806634916491895579936353)
          ·
            refine ⟨12604976187368921684952265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806634916491895579936353 12604976187368921684952265)
            ·
              refine ⟨9453732140526691263714199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12604976187368921684952265 9453732140526691263714199)
              ·
                refine ⟨14180598210790036895571299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453732140526691263714199 14180598210790036895571299)
                ·
                  refine ⟨21270897316185055343356949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14180598210790036895571299 21270897316185055343356949)
                  ·
                    refine ⟨997073311696174469219857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21270897316185055343356949 997073311696174469219857)
                    ·
                      rfl

theorem cell23_5825380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_5825380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5825380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5825380 prefixEnd_5825380 := by exact prefixLift 5825380
  have htrace : WordTrace (prefixWord ++ tailWord_5825380) baseStart_5825380 baseEnd_5825380 := by
    simpa [prefixWord, tailWord_5825380, baseEnd_5825380] using wordTrace_append hprefix tailTrace_5825380
  have hstable : (prefixWord ++ tailWord_5825380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5825380).length < 2 ^ (prefixWord ++ tailWord_5825380).sum := by decide
  have hdescent : baseEnd_5825380 < baseStart_5825380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5825380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
