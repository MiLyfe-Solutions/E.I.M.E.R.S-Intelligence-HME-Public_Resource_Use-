import V185TrunkScan23Chunk0470

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2785903 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_2785903 : Nat := 118140960795 + 2785903 * 2 ^ 59
def prefixEnd_2785903 : Nat := 4983230072969 + 3 ^ 40 * 2785903 * 2
def baseEnd_2785903 : Nat := 1430507295802718875400371

theorem tailTrace_2785903 : CollatzResearch.WordTrace tailWord_2785903 prefixEnd_2785903 1430507295802718875400371 := by
  unfold tailWord_2785903
  simp only [CollatzResearch.WordTrace]
  refine ⟨101610230026156700197586363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67740153350771133465057575 101610230026156700197586363)
  ·
    refine ⟨152415345039235050296379545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101610230026156700197586363 152415345039235050296379545)
    ·
      refine ⟨114311508779426287722284659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152415345039235050296379545 114311508779426287722284659)
      ·
        refine ⟨171467263169139431583426989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114311508779426287722284659 171467263169139431583426989)
        ·
          refine ⟨64300223688427286843785121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171467263169139431583426989 64300223688427286843785121)
          ·
            refine ⟨48225167766320465132838841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64300223688427286843785121 48225167766320465132838841)
            ·
              refine ⟨36168875824740348849629131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48225167766320465132838841 36168875824740348849629131)
              ·
                refine ⟨54253313737110523274443697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36168875824740348849629131 54253313737110523274443697)
                ·
                  refine ⟨40689985302832892455832773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54253313737110523274443697 40689985302832892455832773)
                  ·
                    refine ⟨7629372244281167335468645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40689985302832892455832773 7629372244281167335468645)
                    ·
                      refine ⟨1430507295802718875400371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7629372244281167335468645 1430507295802718875400371)
                      ·
                        rfl

theorem cell23_2785903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_2785903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785903 prefixEnd_2785903 := by exact prefixLift 2785903
  have htrace : WordTrace (prefixWord ++ tailWord_2785903) baseStart_2785903 baseEnd_2785903 := by
    simpa [prefixWord, tailWord_2785903, baseEnd_2785903] using wordTrace_append hprefix tailTrace_2785903
  have hstable : (prefixWord ++ tailWord_2785903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785903).length < 2 ^ (prefixWord ++ tailWord_2785903).sum := by decide
  have hdescent : baseEnd_2785903 < baseStart_2785903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785934 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_2785934 : Nat := 118140960795 + 2785934 * 2 ^ 59
def prefixEnd_2785934 : Nat := 4983230072969 + 3 ^ 40 * 2785934 * 2
def baseEnd_2785934 : Nat := 476841071234336084704243

theorem tailTrace_2785934 : CollatzResearch.WordTrace tailWord_2785934 prefixEnd_2785934 476841071234336084704243 := by
  unfold tailWord_2785934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701420086130549061495607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67740907126029594994643237 12701420086130549061495607)
  ·
    refine ⟨19052130129195823592243411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701420086130549061495607 19052130129195823592243411)
    ·
      refine ⟨28578195193793735388365117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19052130129195823592243411 28578195193793735388365117)
      ·
        refine ⟨10716823197672650770636919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28578195193793735388365117 10716823197672650770636919)
        ·
          refine ⟨16075234796508976155955379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10716823197672650770636919 16075234796508976155955379)
          ·
            refine ⟨24112852194763464233933069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16075234796508976155955379 24112852194763464233933069)
            ·
              refine ⟨9042319573036299087724901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24112852194763464233933069 9042319573036299087724901)
              ·
                refine ⟨1695434919944306078948419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9042319573036299087724901 1695434919944306078948419)
                ·
                  refine ⟨2543152379916459118422629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695434919944306078948419 2543152379916459118422629)
                  ·
                    refine ⟨476841071234336084704243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543152379916459118422629 476841071234336084704243)
                    ·
                      rfl

theorem cell23_2785934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_2785934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785934 prefixEnd_2785934 := by exact prefixLift 2785934
  have htrace : WordTrace (prefixWord ++ tailWord_2785934) baseStart_2785934 baseEnd_2785934 := by
    simpa [prefixWord, tailWord_2785934, baseEnd_2785934] using wordTrace_append hprefix tailTrace_2785934
  have hstable : (prefixWord ++ tailWord_2785934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785934).length < 2 ^ (prefixWord ++ tailWord_2785934).sum := by decide
  have hdescent : baseEnd_2785934 < baseStart_2785934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2785967 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 5, 2]
def baseStart_2785967 : Nat := 118140960795 + 2785967 * 2 ^ 59
def prefixEnd_2785967 : Nat := 4983230072969 + 3 ^ 40 * 2785967 * 2
def baseEnd_2785967 : Nat := 1430540158564606625000077

theorem tailTrace_2785967 : CollatzResearch.WordTrace tailWord_2785967 prefixEnd_2785967 1430540158564606625000077 := by
  unfold tailWord_2785967
  simp only [CollatzResearch.WordTrace]
  refine ⟨101612564297924839127916155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67741709531949892751944103 101612564297924839127916155)
  ·
    refine ⟨152418846446887258691874233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101612564297924839127916155 152418846446887258691874233)
    ·
      refine ⟨114314134835165444018905675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152418846446887258691874233 114314134835165444018905675)
      ·
        refine ⟨171471202252748166028358513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114314134835165444018905675 171471202252748166028358513)
        ·
          refine ⟨128603401689561124521268885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171471202252748166028358513 128603401689561124521268885)
          ·
            refine ⟨6028284454198177711934479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128603401689561124521268885 6028284454198177711934479)
            ·
              refine ⟨9042426681297266567901719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028284454198177711934479 9042426681297266567901719)
              ·
                refine ⟨13563640021945899851852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042426681297266567901719 13563640021945899851852579)
                ·
                  refine ⟨20345460032918849777778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13563640021945899851852579 20345460032918849777778869)
                  ·
                    refine ⟨1907386878086142166666769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20345460032918849777778869 1907386878086142166666769)
                    ·
                      refine ⟨1430540158564606625000077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907386878086142166666769 1430540158564606625000077)
                      ·
                        rfl

theorem cell23_2785967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5, 2].length) (baseStart_2785967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2785967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2785967 prefixEnd_2785967 := by exact prefixLift 2785967
  have htrace : WordTrace (prefixWord ++ tailWord_2785967) baseStart_2785967 baseEnd_2785967 := by
    simpa [prefixWord, tailWord_2785967, baseEnd_2785967] using wordTrace_append hprefix tailTrace_2785967
  have hstable : (prefixWord ++ tailWord_2785967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2785967).length < 2 ^ (prefixWord ++ tailWord_2785967).sum := by decide
  have hdescent : baseEnd_2785967 < baseStart_2785967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2785967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786007 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 6]
def baseStart_2786007 : Nat := 118140960795 + 2786007 * 2 ^ 59
def prefixEnd_2786007 : Nat := 4983230072969 + 3 ^ 40 * 2786007 * 2
def baseEnd_2786007 : Nat := 476853565930262156166631

theorem tailTrace_2786007 : CollatzResearch.WordTrace tailWord_2786007 prefixEnd_2786007 476853565930262156166631 := by
  unfold tailWord_2786007
  simp only [CollatzResearch.WordTrace]
  refine ⟨101614023217779925959372275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67742682145186617306248183 101614023217779925959372275)
  ·
    refine ⟨152421034826669888939058413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101614023217779925959372275 152421034826669888939058413)
    ·
      refine ⟨57157888060001208352146905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152421034826669888939058413 57157888060001208352146905)
      ·
        refine ⟨42868416045000906264110179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57157888060001208352146905 42868416045000906264110179)
        ·
          refine ⟨64302624067501359396165269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42868416045000906264110179 64302624067501359396165269)
          ·
            refine ⟨3014185503164126221695247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64302624067501359396165269 3014185503164126221695247)
            ·
              refine ⟨4521278254746189332542871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014185503164126221695247 4521278254746189332542871)
              ·
                refine ⟨6781917382119283998814307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4521278254746189332542871 6781917382119283998814307)
                ·
                  refine ⟨10172876073178925998221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6781917382119283998814307 10172876073178925998221461)
                  ·
                    refine ⟨476853565930262156166631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10172876073178925998221461 476853565930262156166631)
                    ·
                      rfl

theorem cell23_2786007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_2786007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786007 prefixEnd_2786007 := by exact prefixLift 2786007
  have htrace : WordTrace (prefixWord ++ tailWord_2786007) baseStart_2786007 baseEnd_2786007 := by
    simpa [prefixWord, tailWord_2786007, baseEnd_2786007] using wordTrace_append hprefix tailTrace_2786007
  have hstable : (prefixWord ++ tailWord_2786007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786007).length < 2 ^ (prefixWord ++ tailWord_2786007).sum := by decide
  have hdescent : baseEnd_2786007 < baseStart_2786007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786010 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2786010 : Nat := 118140960795 + 2786010 * 2 ^ 59
def prefixEnd_2786010 : Nat := 4983230072969 + 3 ^ 40 * 2786010 * 2
def baseEnd_2786010 : Nat := 1430562238232749956762379

theorem tailTrace_2786010 : CollatzResearch.WordTrace tailWord_2786010 prefixEnd_2786010 1430562238232749956762379 := by
  unfold tailWord_2786010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25403533159192264367932871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67742755091179371647820989 25403533159192264367932871)
  ·
    refine ⟨38105299738788396551899307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25403533159192264367932871 38105299738788396551899307)
    ·
      refine ⟨57157949608182594827848961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38105299738788396551899307 57157949608182594827848961)
      ·
        refine ⟨42868462206136946120886721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57157949608182594827848961 42868462206136946120886721)
        ·
          refine ⟨32151346654602709590665041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42868462206136946120886721 32151346654602709590665041)
          ·
            refine ⟨24113509990952032192998781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32151346654602709590665041 24113509990952032192998781)
            ·
              refine ⟨9042566246607012072374543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24113509990952032192998781 9042566246607012072374543)
              ·
                refine ⟨13563849369910518108561815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042566246607012072374543 13563849369910518108561815)
                ·
                  refine ⟨20345774054865777162842723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13563849369910518108561815 20345774054865777162842723)
                  ·
                    refine ⟨30518661082298665744264085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20345774054865777162842723 30518661082298665744264085)
                    ·
                      refine ⟨1430562238232749956762379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30518661082298665744264085 1430562238232749956762379)
                      ·
                        rfl

theorem cell23_2786010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2786010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786010 prefixEnd_2786010 := by exact prefixLift 2786010
  have htrace : WordTrace (prefixWord ++ tailWord_2786010) baseStart_2786010 baseEnd_2786010 := by
    simpa [prefixWord, tailWord_2786010, baseEnd_2786010] using wordTrace_append hprefix tailTrace_2786010
  have hstable : (prefixWord ++ tailWord_2786010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786010).length < 2 ^ (prefixWord ++ tailWord_2786010).sum := by decide
  have hdescent : baseEnd_2786010 < baseStart_2786010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786020 : List Nat := [2, 3, 1, 1, 1, 5, 1, 9]
def baseStart_2786020 : Nat := 118140960795 + 2786020 * 2 ^ 59
def prefixEnd_2786020 : Nat := 4983230072969 + 3 ^ 40 * 2786020 * 2
def baseEnd_2786020 : Nat := 52983976779233145097679

theorem tailTrace_2786020 : CollatzResearch.WordTrace tailWord_2786020 prefixEnd_2786020 52983976779233145097679 := by
  unfold tailWord_2786020
  simp only [CollatzResearch.WordTrace]
  refine ⟨50807248683366414589797757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67742998244488552786397009 50807248683366414589797757)
  ·
    refine ⟨19052718256262405471174159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50807248683366414589797757 19052718256262405471174159)
    ·
      refine ⟨28579077384393608206761239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19052718256262405471174159 28579077384393608206761239)
      ·
        refine ⟨42868616076590412310141859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28579077384393608206761239 42868616076590412310141859)
        ·
          refine ⟨64302924114885618465212789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42868616076590412310141859 64302924114885618465212789)
          ·
            refine ⟨6028399135770526731113699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64302924114885618465212789 6028399135770526731113699)
            ·
              refine ⟨9042598703655790096670549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6028399135770526731113699 9042598703655790096670549)
              ·
                refine ⟨52983976779233145097679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9042598703655790096670549 52983976779233145097679)
                ·
                  rfl

theorem cell23_2786020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 9].length) (baseStart_2786020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786020 prefixEnd_2786020 := by exact prefixLift 2786020
  have htrace : WordTrace (prefixWord ++ tailWord_2786020) baseStart_2786020 baseEnd_2786020 := by
    simpa [prefixWord, tailWord_2786020, baseEnd_2786020] using wordTrace_append hprefix tailTrace_2786020
  have hstable : (prefixWord ++ tailWord_2786020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786020).length < 2 ^ (prefixWord ++ tailWord_2786020).sum := by decide
  have hdescent : baseEnd_2786020 < baseStart_2786020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786034 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2786034 : Nat := 118140960795 + 2786034 * 2 ^ 59
def prefixEnd_2786034 : Nat := 4983230072969 + 3 ^ 40 * 2786034 * 2
def baseEnd_2786034 : Nat := 1430574561768457862862269

theorem tailTrace_2786034 : CollatzResearch.WordTrace tailWord_2786034 prefixEnd_2786034 1430574561768457862862269 := by
  unfold tailWord_2786034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25403751997170527392651289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67743338659121406380403437 25403751997170527392651289)
  ·
    refine ⟨19052813997877895544488467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25403751997170527392651289 19052813997877895544488467)
    ·
      refine ⟨28579220996816843316732701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19052813997877895544488467 28579220996816843316732701)
      ·
        refine ⟨10717207873806316243774763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28579220996816843316732701 10717207873806316243774763)
        ·
          refine ⟨16075811810709474365662145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10717207873806316243774763 16075811810709474365662145)
          ·
            refine ⟨12056858858032105774246609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16075811810709474365662145 12056858858032105774246609)
            ·
              refine ⟨9042644143524079330684957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12056858858032105774246609 9042644143524079330684957)
              ·
                refine ⟨3390991553821529749006859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9042644143524079330684957 3390991553821529749006859)
                ·
                  refine ⟨5086487330732294623510289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390991553821529749006859 5086487330732294623510289)
                  ·
                    refine ⟨3814865498049220967632717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5086487330732294623510289 3814865498049220967632717)
                    ·
                      refine ⟨1430574561768457862862269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3814865498049220967632717 1430574561768457862862269)
                      ·
                        rfl

theorem cell23_2786034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2786034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786034 prefixEnd_2786034 := by exact prefixLift 2786034
  have htrace : WordTrace (prefixWord ++ tailWord_2786034) baseStart_2786034 baseEnd_2786034 := by
    simpa [prefixWord, tailWord_2786034, baseEnd_2786034] using wordTrace_append hprefix tailTrace_2786034
  have hstable : (prefixWord ++ tailWord_2786034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786034).length < 2 ^ (prefixWord ++ tailWord_2786034).sum := by decide
  have hdescent : baseEnd_2786034 < baseStart_2786034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786074 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_2786074 : Nat := 118140960795 + 2786074 * 2 ^ 59
def prefixEnd_2786074 : Nat := 4983230072969 + 3 ^ 40 * 2786074 * 2
def baseEnd_2786074 : Nat := 1430595100994637706362085

theorem tailTrace_2786074 : CollatzResearch.WordTrace tailWord_2786074 prefixEnd_2786074 1430595100994637706362085 := by
  unfold tailWord_2786074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25404116727134299100515319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67744311272358130934707517 25404116727134299100515319)
  ·
    refine ⟨38106175090701448650772979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25404116727134299100515319 38106175090701448650772979)
    ·
      refine ⟨57159262636052172976159469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38106175090701448650772979 57159262636052172976159469)
      ·
        refine ⟨21434723488519564866059801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57159262636052172976159469 21434723488519564866059801)
        ·
          refine ⟨16076042616389673649544851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21434723488519564866059801 16076042616389673649544851)
          ·
            refine ⟨24114063924584510474317277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16076042616389673649544851 24114063924584510474317277)
            ·
              refine ⟨9042773971719191427868979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24114063924584510474317277 9042773971719191427868979)
              ·
                refine ⟨13564160957578787141803469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9042773971719191427868979 13564160957578787141803469)
                ·
                  refine ⟨5086560359092045178176301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13564160957578787141803469 5086560359092045178176301)
                  ·
                    refine ⟨1907460134659516941816113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5086560359092045178176301 1907460134659516941816113)
                    ·
                      refine ⟨1430595100994637706362085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907460134659516941816113 1430595100994637706362085)
                      ·
                        rfl

theorem cell23_2786074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_2786074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786074 prefixEnd_2786074 := by exact prefixLift 2786074
  have htrace : WordTrace (prefixWord ++ tailWord_2786074) baseStart_2786074 baseEnd_2786074 := by
    simpa [prefixWord, tailWord_2786074, baseEnd_2786074] using wordTrace_append hprefix tailTrace_2786074
  have hstable : (prefixWord ++ tailWord_2786074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786074).length < 2 ^ (prefixWord ++ tailWord_2786074).sum := by decide
  have hdescent : baseEnd_2786074 < baseStart_2786074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786121 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 2, 2, 2]
def baseStart_2786121 : Nat := 118140960795 + 2786121 * 2 ^ 59
def prefixEnd_2786121 : Nat := 4983230072969 + 3 ^ 40 * 2786121 * 2
def baseEnd_2786121 : Nat := 1430619234585399022474369

theorem tailTrace_2786121 : CollatzResearch.WordTrace tailWord_2786121 prefixEnd_2786121 1430619234585399022474369 := by
  unfold tailWord_2786121
  simp only [CollatzResearch.WordTrace]
  refine ⟨101618181139366923429022217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67745454092911282286014811 101618181139366923429022217)
  ·
    refine ⟨76213635854525192571766663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101618181139366923429022217 76213635854525192571766663)
    ·
      refine ⟨114320453781787788857649995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76213635854525192571766663 114320453781787788857649995)
      ·
        refine ⟨171480680672681683286474993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114320453781787788857649995 171480680672681683286474993)
        ·
          refine ⟨128610510504511262464856245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171480680672681683286474993 128610510504511262464856245)
          ·
            refine ⟨12057235359797930856080273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128610510504511262464856245 12057235359797930856080273)
            ·
              refine ⟨9042926519848448142060205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12057235359797930856080273 9042926519848448142060205)
              ·
                refine ⟨3391097444943168053272577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9042926519848448142060205 3391097444943168053272577)
                ·
                  refine ⟨2543323083707376039954433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391097444943168053272577 2543323083707376039954433)
                  ·
                    refine ⟨1907492312780532029965825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543323083707376039954433 1907492312780532029965825)
                    ·
                      refine ⟨1430619234585399022474369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907492312780532029965825 1430619234585399022474369)
                      ·
                        rfl

theorem cell23_2786121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2, 2].length) (baseStart_2786121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786121 prefixEnd_2786121 := by exact prefixLift 2786121
  have htrace : WordTrace (prefixWord ++ tailWord_2786121) baseStart_2786121 baseEnd_2786121 := by
    simpa [prefixWord, tailWord_2786121, baseEnd_2786121] using wordTrace_append hprefix tailTrace_2786121
  have hstable : (prefixWord ++ tailWord_2786121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786121).length < 2 ^ (prefixWord ++ tailWord_2786121).sum := by decide
  have hdescent : baseEnd_2786121 < baseStart_2786121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786144 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 5]
def baseStart_2786144 : Nat := 118140960795 + 2786144 * 2 ^ 59
def prefixEnd_2786144 : Nat := 4983230072969 + 3 ^ 40 * 2786144 * 2
def baseEnd_2786144 : Nat := 158959004960050270276307

theorem tailTrace_2786144 : CollatzResearch.WordTrace tailWord_2786144 prefixEnd_2786144 158959004960050270276307 := by
  unfold tailWord_2786144
  simp only [CollatzResearch.WordTrace]
  refine ⟨50809510009141799178554743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67746013345522398904739657 50809510009141799178554743)
  ·
    refine ⟨76214265013712698767832115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50809510009141799178554743 76214265013712698767832115)
    ·
      refine ⟨114321397520569048151748173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76214265013712698767832115 114321397520569048151748173)
      ·
        refine ⟨42870524070213393056905565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114321397520569048151748173 42870524070213393056905565)
        ·
          refine ⟨16076446526330022396339587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42870524070213393056905565 16076446526330022396339587)
          ·
            refine ⟨24114669789495033594509381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16076446526330022396339587 24114669789495033594509381)
            ·
              refine ⟨4521500585530318798970509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24114669789495033594509381 4521500585530318798970509)
              ·
                refine ⟨1695562719573869549613941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4521500585530318798970509 1695562719573869549613941)
                ·
                  refine ⟨158959004960050270276307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1695562719573869549613941 158959004960050270276307)
                  ·
                    rfl

theorem cell23_2786144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 5].length) (baseStart_2786144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786144 prefixEnd_2786144 := by exact prefixLift 2786144
  have htrace : WordTrace (prefixWord ++ tailWord_2786144) baseStart_2786144 baseEnd_2786144 := by
    simpa [prefixWord, tailWord_2786144, baseEnd_2786144] using wordTrace_append hprefix tailTrace_2786144
  have hstable : (prefixWord ++ tailWord_2786144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786144).length < 2 ^ (prefixWord ++ tailWord_2786144).sum := by decide
  have hdescent : baseEnd_2786144 < baseStart_2786144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786157 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2786157 : Nat := 118140960795 + 2786157 * 2 ^ 59
def prefixEnd_2786157 : Nat := 4983230072969 + 3 ^ 40 * 2786157 * 2
def baseEnd_2786157 : Nat := 476879239962986960541401

theorem tailTrace_2786157 : CollatzResearch.WordTrace tailWord_2786157 prefixEnd_2786157 476879239962986960541401 := by
  unfold tailWord_2786157
  simp only [CollatzResearch.WordTrace]
  refine ⟨101619494167236501577332725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67746329444824334384888483 101619494167236501577332725)
  ·
    refine ⟨9526827578178422022874943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101619494167236501577332725 9526827578178422022874943)
    ·
      refine ⟨14290241367267633034312415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526827578178422022874943 14290241367267633034312415)
      ·
        refine ⟨21435362050901449551468623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290241367267633034312415 21435362050901449551468623)
        ·
          refine ⟨32153043076352174327202935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21435362050901449551468623 32153043076352174327202935)
          ·
            refine ⟨48229564614528261490804403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32153043076352174327202935 48229564614528261490804403)
            ·
              refine ⟨72344346921792392236206605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48229564614528261490804403 72344346921792392236206605)
              ·
                refine ⟨27129130095672147088577477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72344346921792392236206605 27129130095672147088577477)
                ·
                  refine ⟨5086711892938527579108277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27129130095672147088577477 5086711892938527579108277)
                  ·
                    refine ⟨476879239962986960541401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5086711892938527579108277 476879239962986960541401)
                    ·
                      rfl

theorem cell23_2786157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2786157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786157 prefixEnd_2786157 := by exact prefixLift 2786157
  have htrace : WordTrace (prefixWord ++ tailWord_2786157) baseStart_2786157 baseEnd_2786157 := by
    simpa [prefixWord, tailWord_2786157, baseEnd_2786157] using wordTrace_append hprefix tailTrace_2786157
  have hstable : (prefixWord ++ tailWord_2786157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786157).length < 2 ^ (prefixWord ++ tailWord_2786157).sum := by decide
  have hdescent : baseEnd_2786157 < baseStart_2786157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786217 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 6]
def baseStart_2786217 : Nat := 118140960795 + 2786217 * 2 ^ 59
def prefixEnd_2786217 : Nat := 4983230072969 + 3 ^ 40 * 2786217 * 2
def baseEnd_2786217 : Nat := 158963169858692294097103

theorem tailTrace_2786217 : CollatzResearch.WordTrace tailWord_2786217 prefixEnd_2786217 158963169858692294097103 := by
  unfold tailWord_2786217
  simp only [CollatzResearch.WordTrace]
  refine ⟨101621682547019131824516905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67747788364679421216344603 101621682547019131824516905)
  ·
    refine ⟨76216261910264348868387679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101621682547019131824516905 76216261910264348868387679)
    ·
      refine ⟨114324392865396523302581519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76216261910264348868387679 114324392865396523302581519)
      ·
        refine ⟨171486589298094784953872279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114324392865396523302581519 171486589298094784953872279)
        ·
          refine ⟨257229883947142177430808419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171486589298094784953872279 257229883947142177430808419)
          ·
            refine ⟨385844825920713266146212629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257229883947142177430808419 385844825920713266146212629)
            ·
              refine ⟨18086476215033434350603717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 385844825920713266146212629 18086476215033434350603717)
              ·
                refine ⟨3391214290318768940738197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18086476215033434350603717 3391214290318768940738197)
                ·
                  refine ⟨158963169858692294097103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3391214290318768940738197 158963169858692294097103)
                  ·
                    rfl

theorem cell23_2786217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_2786217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786217 prefixEnd_2786217 := by exact prefixLift 2786217
  have htrace : WordTrace (prefixWord ++ tailWord_2786217) baseStart_2786217 baseEnd_2786217 := by
    simpa [prefixWord, tailWord_2786217, baseEnd_2786217] using wordTrace_append hprefix tailTrace_2786217
  have hstable : (prefixWord ++ tailWord_2786217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786217).length < 2 ^ (prefixWord ++ tailWord_2786217).sum := by decide
  have hdescent : baseEnd_2786217 < baseStart_2786217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786227 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3]
def baseStart_2786227 : Nat := 118140960795 + 2786227 * 2 ^ 59
def prefixEnd_2786227 : Nat := 4983230072969 + 3 ^ 40 * 2786227 * 2
def baseEnd_2786227 : Nat := 1430673663534775607748881

theorem tailTrace_2786227 : CollatzResearch.WordTrace tailWord_2786227 prefixEnd_2786227 1430673663534775607748881 := by
  unfold tailWord_2786227
  simp only [CollatzResearch.WordTrace]
  refine ⟨101622047276982903532380935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67748031517988602354920623 101622047276982903532380935)
  ·
    refine ⟨152433070915474355298571403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101622047276982903532380935 152433070915474355298571403)
    ·
      refine ⟨228649606373211532947857105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152433070915474355298571403 228649606373211532947857105)
      ·
        refine ⟨171487204779908649710892829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228649606373211532947857105 171487204779908649710892829)
        ·
          refine ⟨64307701792465743641584811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171487204779908649710892829 64307701792465743641584811)
          ·
            refine ⟨96461552688698615462377217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64307701792465743641584811 96461552688698615462377217)
            ·
              refine ⟨72346164516523961596782913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96461552688698615462377217 72346164516523961596782913)
              ·
                refine ⟨54259623387392971197587185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72346164516523961596782913 54259623387392971197587185)
                ·
                  refine ⟨40694717540544728398190389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54259623387392971197587185 40694717540544728398190389)
                  ·
                    refine ⟨3815129769426068287330349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40694717540544728398190389 3815129769426068287330349)
                    ·
                      refine ⟨1430673663534775607748881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815129769426068287330349 1430673663534775607748881)
                      ·
                        rfl

theorem cell23_2786227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_2786227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786227 prefixEnd_2786227 := by exact prefixLift 2786227
  have htrace : WordTrace (prefixWord ++ tailWord_2786227) baseStart_2786227 baseEnd_2786227 := by
    simpa [prefixWord, tailWord_2786227, baseEnd_2786227] using wordTrace_append hprefix tailTrace_2786227
  have hstable : (prefixWord ++ tailWord_2786227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786227).length < 2 ^ (prefixWord ++ tailWord_2786227).sum := by decide
  have hdescent : baseEnd_2786227 < baseStart_2786227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786284 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_2786284 : Nat := 118140960795 + 2786284 * 2 ^ 59
def prefixEnd_2786284 : Nat := 4983230072969 + 3 ^ 40 * 2786284 * 2
def baseEnd_2786284 : Nat := 1430702931932081884736119

theorem tailTrace_2786284 : CollatzResearch.WordTrace tailWord_2786284 prefixEnd_2786284 1430702931932081884736119 := by
  unfold tailWord_2786284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812063118888201133602953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67749417491850934844803937 50812063118888201133602953)
  ·
    refine ⟨38109047339166150850202215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50812063118888201133602953 38109047339166150850202215)
    ·
      refine ⟨57163571008749226275303323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38109047339166150850202215 57163571008749226275303323)
      ·
        refine ⟨85745356513123839412954985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57163571008749226275303323 85745356513123839412954985)
        ·
          refine ⟨64309017384842879559716239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85745356513123839412954985 64309017384842879559716239)
          ·
            refine ⟨96463526077264319339574359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64309017384842879559716239 96463526077264319339574359)
            ·
              refine ⟨144695289115896479009361539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96463526077264319339574359 144695289115896479009361539)
              ·
                refine ⟨217042933673844718514042309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144695289115896479009361539 217042933673844718514042309)
                ·
                  refine ⟨40695550063845884721382933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217042933673844718514042309 40695550063845884721382933)
                  ·
                    refine ⟨1907603909242775846314825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40695550063845884721382933 1907603909242775846314825)
                    ·
                      refine ⟨1430702931932081884736119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907603909242775846314825 1430702931932081884736119)
                      ·
                        rfl

theorem cell23_2786284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_2786284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786284 prefixEnd_2786284 := by exact prefixLift 2786284
  have htrace : WordTrace (prefixWord ++ tailWord_2786284) baseStart_2786284 baseEnd_2786284 := by
    simpa [prefixWord, tailWord_2786284, baseEnd_2786284] using wordTrace_append hprefix tailTrace_2786284
  have hstable : (prefixWord ++ tailWord_2786284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786284).length < 2 ^ (prefixWord ++ tailWord_2786284).sum := by decide
  have hdescent : baseEnd_2786284 < baseStart_2786284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786318 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_2786318 : Nat := 118140960795 + 2786318 * 2 ^ 59
def prefixEnd_2786318 : Nat := 4983230072969 + 3 ^ 40 * 2786318 * 2
def baseEnd_2786318 : Nat := 1430720390274334751710963

theorem tailTrace_2786318 : CollatzResearch.WordTrace tailWord_2786318 prefixEnd_2786318 1430720390274334751710963 := by
  unfold tailWord_2786318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12703170789956653259242951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67750244213102150715962405 12703170789956653259242951)
  ·
    refine ⟨19054756184934979888864427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12703170789956653259242951 19054756184934979888864427)
    ·
      refine ⟨28582134277402469833296641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19054756184934979888864427 28582134277402469833296641)
      ·
        refine ⟨21436600708051852374972481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28582134277402469833296641 21436600708051852374972481)
        ·
          refine ⟨16077450531038889281229361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21436600708051852374972481 16077450531038889281229361)
          ·
            refine ⟨12058087898279166960922021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16077450531038889281229361 12058087898279166960922021)
            ·
              refine ⟨2260891480927343805172879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12058087898279166960922021 2260891480927343805172879)
              ·
                refine ⟨3391337221391015707759319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260891480927343805172879 3391337221391015707759319)
                ·
                  refine ⟨5087005832086523561638979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391337221391015707759319 5087005832086523561638979)
                  ·
                    refine ⟨7630508748129785342458469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087005832086523561638979 7630508748129785342458469)
                    ·
                      refine ⟨1430720390274334751710963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7630508748129785342458469 1430720390274334751710963)
                      ·
                        rfl

theorem cell23_2786318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_2786318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786318 prefixEnd_2786318 := by exact prefixLift 2786318
  have htrace : WordTrace (prefixWord ++ tailWord_2786318) baseStart_2786318 baseEnd_2786318 := by
    simpa [prefixWord, tailWord_2786318, baseEnd_2786318] using wordTrace_append hprefix tailTrace_2786318
  have hstable : (prefixWord ++ tailWord_2786318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786318).length < 2 ^ (prefixWord ++ tailWord_2786318).sum := by decide
  have hdescent : baseEnd_2786318 < baseStart_2786318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786328 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_2786328 : Nat := 118140960795 + 2786328 * 2 ^ 59
def prefixEnd_2786328 : Nat := 4983230072969 + 3 ^ 40 * 2786328 * 2
def baseEnd_2786328 : Nat := 476908508360293237528639

theorem tailTrace_2786328 : CollatzResearch.WordTrace tailWord_2786328 prefixEnd_2786328 476908508360293237528639 := by
  unfold tailWord_2786328
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812865524808498890903819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67750487366411331854538425 50812865524808498890903819)
  ·
    refine ⟨76219298287212748336355729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50812865524808498890903819 76219298287212748336355729)
    ·
      refine ⟨57164473715409561252266797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76219298287212748336355729 57164473715409561252266797)
      ·
        refine ⟨21436677643278585469600049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57164473715409561252266797 21436677643278585469600049)
        ·
          refine ⟨16077508232458939102200037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21436677643278585469600049 16077508232458939102200037)
          ·
            refine ⟨3014532793586051081662507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16077508232458939102200037 3014532793586051081662507)
            ·
              refine ⟨4521799190379076622493761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014532793586051081662507 4521799190379076622493761)
              ·
                refine ⟨3391349392784307466870321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521799190379076622493761 3391349392784307466870321)
                ·
                  refine ⟨2543512044588230600152741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391349392784307466870321 2543512044588230600152741)
                  ·
                    refine ⟨476908508360293237528639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2543512044588230600152741 476908508360293237528639)
                    ·
                      rfl

theorem cell23_2786328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_2786328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786328 prefixEnd_2786328 := by exact prefixLift 2786328
  have htrace : WordTrace (prefixWord ++ tailWord_2786328) baseStart_2786328 baseEnd_2786328 := by
    simpa [prefixWord, tailWord_2786328, baseEnd_2786328] using wordTrace_append hprefix tailTrace_2786328
  have hstable : (prefixWord ++ tailWord_2786328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786328).length < 2 ^ (prefixWord ++ tailWord_2786328).sum := by decide
  have hdescent : baseEnd_2786328 < baseStart_2786328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786335 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 1, 2, 2]
def baseStart_2786335 : Nat := 118140960795 + 2786335 * 2 ^ 59
def prefixEnd_2786335 : Nat := 4983230072969 + 3 ^ 40 * 2786335 * 2
def baseEnd_2786335 : Nat := 1430729119445461185198385

theorem tailTrace_2786335 : CollatzResearch.WordTrace tailWord_2786335 prefixEnd_2786335 1430729119445461185198385 := by
  unfold tailWord_2786335
  simp only [CollatzResearch.WordTrace]
  refine ⟨101625986360591637977312459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67750657573727758651541639 101625986360591637977312459)
  ·
    refine ⟨152438979540887456965968689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101625986360591637977312459 152438979540887456965968689)
    ·
      refine ⟨114329234655665592724476517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152438979540887456965968689 114329234655665592724476517)
      ·
        refine ⟨21436731497937298635839347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114329234655665592724476517 21436731497937298635839347)
        ·
          refine ⟨32155097246905947953759021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436731497937298635839347 32155097246905947953759021)
          ·
            refine ⟨12058161467589730482659633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32155097246905947953759021 12058161467589730482659633)
            ·
              refine ⟨9043621100692297861994725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058161467589730482659633 9043621100692297861994725)
              ·
                refine ⟨1695678956379805849124011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9043621100692297861994725 1695678956379805849124011)
                ·
                  refine ⟨2543518434569708773686017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695678956379805849124011 2543518434569708773686017)
                  ·
                    refine ⟨1907638825927281580264513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543518434569708773686017 1907638825927281580264513)
                    ·
                      refine ⟨1430729119445461185198385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907638825927281580264513 1430729119445461185198385)
                      ·
                        rfl

theorem cell23_2786335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_2786335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786335 prefixEnd_2786335 := by exact prefixLift 2786335
  have htrace : WordTrace (prefixWord ++ tailWord_2786335) baseStart_2786335 baseEnd_2786335 := by
    simpa [prefixWord, tailWord_2786335, baseEnd_2786335] using wordTrace_append hprefix tailTrace_2786335
  have hstable : (prefixWord ++ tailWord_2786335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786335).length < 2 ^ (prefixWord ++ tailWord_2786335).sum := by decide
  have hdescent : baseEnd_2786335 < baseStart_2786335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786358 : List Nat := [5, 1, 2, 1, 1, 4, 2, 7]
def baseStart_2786358 : Nat := 118140960795 + 2786358 * 2 ^ 59
def prefixEnd_2786358 : Nat := 4983230072969 + 3 ^ 40 * 2786358 * 2
def baseEnd_2786358 : Nat := 52990404796315355378177

theorem tailTrace_2786358 : CollatzResearch.WordTrace tailWord_2786358 prefixEnd_2786358 52990404796315355378177 := by
  unfold tailWord_2786358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351676577469269556587483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67751216826338875270266485 6351676577469269556587483)
  ·
    refine ⟨9527514866203904334881225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351676577469269556587483 9527514866203904334881225)
    ·
      refine ⟨7145636149652928251160919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9527514866203904334881225 7145636149652928251160919)
      ·
        refine ⟨10718454224479392376741379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145636149652928251160919 10718454224479392376741379)
        ·
          refine ⟨16077681336719088565112069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10718454224479392376741379 16077681336719088565112069)
          ·
            refine ⟨3014565250634829105958513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16077681336719088565112069 3014565250634829105958513)
            ·
              refine ⟨2260923937976121829468885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014565250634829105958513 2260923937976121829468885)
              ·
                refine ⟨52990404796315355378177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2260923937976121829468885 52990404796315355378177)
                ·
                  rfl

theorem cell23_2786358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_2786358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786358 prefixEnd_2786358 := by exact prefixLift 2786358
  have htrace : WordTrace (prefixWord ++ tailWord_2786358) baseStart_2786358 baseEnd_2786358 := by
    simpa [prefixWord, tailWord_2786358, baseEnd_2786358] using wordTrace_append hprefix tailTrace_2786358
  have hstable : (prefixWord ++ tailWord_2786358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786358).length < 2 ^ (prefixWord ++ tailWord_2786358).sum := by decide
  have hdescent : baseEnd_2786358 < baseStart_2786358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786364 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2786364 : Nat := 118140960795 + 2786364 * 2 ^ 59
def prefixEnd_2786364 : Nat := 4983230072969 + 3 ^ 40 * 2786364 * 2
def baseEnd_2786364 : Nat := 1430744010384441571735751

theorem tailTrace_2786364 : CollatzResearch.WordTrace tailWord_2786364 prefixEnd_2786364 1430744010384441571735751 := by
  unfold tailWord_2786364
  simp only [CollatzResearch.WordTrace]
  refine ⟨50813522038743287965059073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67751362718324383953412097 50813522038743287965059073)
  ·
    refine ⟨38110141529057465973794305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50813522038743287965059073 38110141529057465973794305)
    ·
      refine ⟨28582606146793099480345729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38110141529057465973794305 28582606146793099480345729)
      ·
        refine ⟨21436954610094824610259297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28582606146793099480345729 21436954610094824610259297)
        ·
          refine ⟨16077715957571118457694473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21436954610094824610259297 16077715957571118457694473)
          ·
            refine ⟨12058286968178338843270855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16077715957571118457694473 12058286968178338843270855)
            ·
              refine ⟨18087430452267508264906283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12058286968178338843270855 18087430452267508264906283)
              ·
                refine ⟨27131145678401262397359425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087430452267508264906283 27131145678401262397359425)
                ·
                  refine ⟨20348359258800946798019569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27131145678401262397359425 20348359258800946798019569)
                  ·
                    refine ⟨15261269444100710098514677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20348359258800946798019569 15261269444100710098514677)
                    ·
                      refine ⟨1430744010384441571735751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15261269444100710098514677 1430744010384441571735751)
                      ·
                        rfl

theorem cell23_2786364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2786364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786364 prefixEnd_2786364 := by exact prefixLift 2786364
  have htrace : WordTrace (prefixWord ++ tailWord_2786364) baseStart_2786364 baseEnd_2786364 := by
    simpa [prefixWord, tailWord_2786364, baseEnd_2786364] using wordTrace_append hprefix tailTrace_2786364
  have hstable : (prefixWord ++ tailWord_2786364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786364).length < 2 ^ (prefixWord ++ tailWord_2786364).sum := by decide
  have hdescent : baseEnd_2786364 < baseStart_2786364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786369 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2786369 : Nat := 118140960795 + 2786369 * 2 ^ 59
def prefixEnd_2786369 : Nat := 4983230072969 + 3 ^ 40 * 2786369 * 2
def baseEnd_2786369 : Nat := 1430746577787714052173229

theorem tailTrace_2786369 : CollatzResearch.WordTrace tailWord_2786369 prefixEnd_2786369 1430746577787714052173229 := by
  unfold tailWord_2786369
  simp only [CollatzResearch.WordTrace]
  refine ⟨101627226442468461784050161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67751484294978974522700107 101627226442468461784050161)
  ·
    refine ⟨76220419831851346338037621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101627226442468461784050161 76220419831851346338037621)
    ·
      refine ⟨7145664359236063719191027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76220419831851346338037621 7145664359236063719191027)
      ·
        refine ⟨10718496538854095578786541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145664359236063719191027 10718496538854095578786541)
        ·
          refine ⟨4019436202070285842044953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10718496538854095578786541 4019436202070285842044953)
          ·
            refine ⟨3014577151552714381533715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4019436202070285842044953 3014577151552714381533715)
            ·
              refine ⟨4521865727329071572300573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014577151552714381533715 4521865727329071572300573)
              ·
                refine ⟨1695699647748401839612715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4521865727329071572300573 1695699647748401839612715)
                ·
                  refine ⟨2543549471622602759419073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695699647748401839612715 2543549471622602759419073)
                  ·
                    refine ⟨1907662103716952069564305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543549471622602759419073 1907662103716952069564305)
                    ·
                      refine ⟨1430746577787714052173229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907662103716952069564305 1430746577787714052173229)
                      ·
                        rfl

theorem cell23_2786369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2786369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786369 prefixEnd_2786369 := by exact prefixLift 2786369
  have htrace : WordTrace (prefixWord ++ tailWord_2786369) baseStart_2786369 baseEnd_2786369 := by
    simpa [prefixWord, tailWord_2786369, baseEnd_2786369] using wordTrace_append hprefix tailTrace_2786369
  have hstable : (prefixWord ++ tailWord_2786369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786369).length < 2 ^ (prefixWord ++ tailWord_2786369).sum := by decide
  have hdescent : baseEnd_2786369 < baseStart_2786369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786378 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_2786378 : Nat := 118140960795 + 2786378 * 2 ^ 59
def prefixEnd_2786378 : Nat := 4983230072969 + 3 ^ 40 * 2786378 * 2
def baseEnd_2786378 : Nat := 1430751199113604516960687

theorem tailTrace_2786378 : CollatzResearch.WordTrace tailWord_2786378 prefixEnd_2786378 1430751199113604516960687 := by
  unfold tailWord_2786378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406888674858964080281947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67751703132957237547418525 25406888674858964080281947)
  ·
    refine ⟨38110333012288446120422921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25406888674858964080281947 38110333012288446120422921)
    ·
      refine ⟨28582749759216334590317191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38110333012288446120422921 28582749759216334590317191)
      ·
        refine ⟨42874124638824501885475787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28582749759216334590317191 42874124638824501885475787)
        ·
          refine ⟨64311186958236752828213681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42874124638824501885475787 64311186958236752828213681)
          ·
            refine ⟨48233390218677564621160261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64311186958236752828213681 48233390218677564621160261)
            ·
              refine ⟨9043760666002043366467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48233390218677564621160261 9043760666002043366467549)
              ·
                refine ⟨3391410249750766262425331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9043760666002043366467549 3391410249750766262425331)
                ·
                  refine ⟨5087115374626149393637997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391410249750766262425331 5087115374626149393637997)
                  ·
                    refine ⟨1907668265484806022614249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5087115374626149393637997 1907668265484806022614249)
                    ·
                      refine ⟨1430751199113604516960687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907668265484806022614249 1430751199113604516960687)
                      ·
                        rfl

theorem cell23_2786378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_2786378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786378 prefixEnd_2786378 := by exact prefixLift 2786378
  have htrace : WordTrace (prefixWord ++ tailWord_2786378) baseStart_2786378 baseEnd_2786378 := by
    simpa [prefixWord, tailWord_2786378, baseEnd_2786378] using wordTrace_append hprefix tailTrace_2786378
  have hstable : (prefixWord ++ tailWord_2786378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786378).length < 2 ^ (prefixWord ++ tailWord_2786378).sum := by decide
  have hdescent : baseEnd_2786378 < baseStart_2786378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786402 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2786402 : Nat := 118140960795 + 2786402 * 2 ^ 59
def prefixEnd_2786402 : Nat := 4983230072969 + 3 ^ 40 * 2786402 * 2
def baseEnd_2786402 : Nat := 1430763522649312423060577

theorem tailTrace_2786402 : CollatzResearch.WordTrace tailWord_2786402 prefixEnd_2786402 1430763522649312423060577 := by
  unfold tailWord_2786402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407107512837227105000365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67752286700899272280000973 25407107512837227105000365)
  ·
    refine ⟨9527665317313960164375137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25407107512837227105000365 9527665317313960164375137)
    ·
      refine ⟨7145748987985470123281353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9527665317313960164375137 7145748987985470123281353)
      ·
        refine ⟨5359311740989102592461015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7145748987985470123281353 5359311740989102592461015)
        ·
          refine ⟨8038967611483653888691523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359311740989102592461015 8038967611483653888691523)
          ·
            refine ⟨12058451417225480833037285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038967611483653888691523 12058451417225480833037285)
            ·
              refine ⟨2260959640729777656194491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12058451417225480833037285 2260959640729777656194491)
              ·
                refine ⟨3391439461094666484291737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260959640729777656194491 3391439461094666484291737)
                ·
                  refine ⟨2543579595820999863218803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391439461094666484291737 2543579595820999863218803)
                  ·
                    refine ⟨3815369393731499794828205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2543579595820999863218803 3815369393731499794828205)
                    ·
                      refine ⟨1430763522649312423060577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815369393731499794828205 1430763522649312423060577)
                      ·
                        rfl

theorem cell23_2786402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2786402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786402 prefixEnd_2786402 := by exact prefixLift 2786402
  have htrace : WordTrace (prefixWord ++ tailWord_2786402) baseStart_2786402 baseEnd_2786402 := by
    simpa [prefixWord, tailWord_2786402, baseEnd_2786402] using wordTrace_append hprefix tailTrace_2786402
  have hstable : (prefixWord ++ tailWord_2786402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786402).length < 2 ^ (prefixWord ++ tailWord_2786402).sum := by decide
  have hdescent : baseEnd_2786402 < baseStart_2786402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786404 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2786404 : Nat := 118140960795 + 2786404 * 2 ^ 59
def prefixEnd_2786404 : Nat := 4983230072969 + 3 ^ 40 * 2786404 * 2
def baseEnd_2786404 : Nat := 1430764549610621415235567

theorem tailTrace_2786404 : CollatzResearch.WordTrace tailWord_2786404 prefixEnd_2786404 1430764549610621415235567 := by
  unfold tailWord_2786404
  simp only [CollatzResearch.WordTrace]
  refine ⟨50814251498670831380787133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67752335331561108507716177 50814251498670831380787133)
  ·
    refine ⟨19055344312001561767795175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50814251498670831380787133 19055344312001561767795175)
    ·
      refine ⟨28583016468002342651692763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19055344312001561767795175 28583016468002342651692763)
      ·
        refine ⟨42874524702003513977539145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28583016468002342651692763 42874524702003513977539145)
        ·
          refine ⟨32155893526502635483154359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42874524702003513977539145 32155893526502635483154359)
          ·
            refine ⟨48233840289753953224731539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32155893526502635483154359 48233840289753953224731539)
            ·
              refine ⟨72350760434630929837097309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48233840289753953224731539 72350760434630929837097309)
              ·
                refine ⟨27131535162986598688911491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72350760434630929837097309 27131535162986598688911491)
                ·
                  refine ⟨40697302744479898033367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27131535162986598688911491 40697302744479898033367237)
                  ·
                    refine ⟨7630744264589980881256357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40697302744479898033367237 7630744264589980881256357)
                    ·
                      refine ⟨1430764549610621415235567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7630744264589980881256357 1430764549610621415235567)
                      ·
                        rfl

theorem cell23_2786404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2786404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786404 prefixEnd_2786404 := by exact prefixLift 2786404
  have htrace : WordTrace (prefixWord ++ tailWord_2786404) baseStart_2786404 baseEnd_2786404 := by
    simpa [prefixWord, tailWord_2786404, baseEnd_2786404] using wordTrace_append hprefix tailTrace_2786404
  have hstable : (prefixWord ++ tailWord_2786404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786404).length < 2 ^ (prefixWord ++ tailWord_2786404).sum := by decide
  have hdescent : baseEnd_2786404 < baseStart_2786404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786451 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 5, 2]
def baseStart_2786451 : Nat := 118140960795 + 2786451 * 2 ^ 59
def prefixEnd_2786451 : Nat := 4983230072969 + 3 ^ 40 * 2786451 * 2
def baseEnd_2786451 : Nat := 1430788683201382731347851

theorem tailTrace_2786451 : CollatzResearch.WordTrace tailWord_2786451 prefixEnd_2786451 1430788683201382731347851 := by
  unfold tailWord_2786451
  simp only [CollatzResearch.WordTrace]
  refine ⟨101630217228171389788535207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67753478152114259859023471 101630217228171389788535207)
  ·
    refine ⟨152445325842257084682802811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101630217228171389788535207 152445325842257084682802811)
    ·
      refine ⟨228667988763385627024204217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152445325842257084682802811 228667988763385627024204217)
      ·
        refine ⟨171500991572539220268153163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228667988763385627024204217 171500991572539220268153163)
        ·
          refine ⟨257251487358808830402229745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171500991572539220268153163 257251487358808830402229745)
          ·
            refine ⟨192938615519106622801672309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257251487358808830402229745 192938615519106622801672309)
            ·
              refine ⟨18087995204916245887656779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192938615519106622801672309 18087995204916245887656779)
              ·
                refine ⟨27131992807374368831485169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18087995204916245887656779 27131992807374368831485169)
                ·
                  refine ⟨20348994605530776623613877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27131992807374368831485169 20348994605530776623613877)
                  ·
                    refine ⟨1907718244268510308463801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20348994605530776623613877 1907718244268510308463801)
                    ·
                      refine ⟨1430788683201382731347851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907718244268510308463801 1430788683201382731347851)
                      ·
                        rfl

theorem cell23_2786451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5, 2].length) (baseStart_2786451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786451 prefixEnd_2786451 := by exact prefixLift 2786451
  have htrace : WordTrace (prefixWord ++ tailWord_2786451) baseStart_2786451 baseEnd_2786451 := by
    simpa [prefixWord, tailWord_2786451, baseEnd_2786451] using wordTrace_append hprefix tailTrace_2786451
  have hstable : (prefixWord ++ tailWord_2786451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786451).length < 2 ^ (prefixWord ++ tailWord_2786451).sum := by decide
  have hdescent : baseEnd_2786451 < baseStart_2786451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786458 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2786458 : Nat := 118140960795 + 2786458 * 2 ^ 59
def prefixEnd_2786458 : Nat := 4983230072969 + 3 ^ 40 * 2786458 * 2
def baseEnd_2786458 : Nat := 1430792277565964203960319

theorem tailTrace_2786458 : CollatzResearch.WordTrace tailWord_2786458 prefixEnd_2786458 1430792277565964203960319 := by
  unfold tailWord_2786458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407618134786507496010007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67753648359430686656026685 25407618134786507496010007)
  ·
    refine ⟨38111427202179761244015011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25407618134786507496010007 38111427202179761244015011)
    ·
      refine ⟨57167140803269641866022517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38111427202179761244015011 57167140803269641866022517)
      ·
        refine ⟨5359419450306528924939611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57167140803269641866022517 5359419450306528924939611)
        ·
          refine ⟨8039129175459793387409417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359419450306528924939611 8039129175459793387409417)
          ·
            refine ⟨6029346881594845040557063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8039129175459793387409417 6029346881594845040557063)
            ·
              refine ⟨9044020322392267560835595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029346881594845040557063 9044020322392267560835595)
              ·
                refine ⟨13566030483588401341253393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9044020322392267560835595 13566030483588401341253393)
                ·
                  refine ⟨10174522862691301005940045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13566030483588401341253393 10174522862691301005940045)
                  ·
                    refine ⟨3815446073509237877227517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10174522862691301005940045 3815446073509237877227517)
                    ·
                      refine ⟨1430792277565964203960319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815446073509237877227517 1430792277565964203960319)
                      ·
                        rfl

theorem cell23_2786458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2786458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786458 prefixEnd_2786458 := by exact prefixLift 2786458
  have htrace : WordTrace (prefixWord ++ tailWord_2786458) baseStart_2786458 baseEnd_2786458 := by
    simpa [prefixWord, tailWord_2786458, baseEnd_2786458] using wordTrace_append hprefix tailTrace_2786458
  have hstable : (prefixWord ++ tailWord_2786458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786458).length < 2 ^ (prefixWord ++ tailWord_2786458).sum := by decide
  have hdescent : baseEnd_2786458 < baseStart_2786458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786501 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_2786501 : Nat := 118140960795 + 2786501 * 2 ^ 59
def prefixEnd_2786501 : Nat := 4983230072969 + 3 ^ 40 * 2786501 * 2
def baseEnd_2786501 : Nat := 1430814357234107535722621

theorem tailTrace_2786501 : CollatzResearch.WordTrace tailWord_2786501 prefixEnd_2786501 1430814357234107535722621 := by
  unfold tailWord_2786501
  simp only [CollatzResearch.WordTrace]
  refine ⟨101632040877990248327855357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67754693918660165551903571 101632040877990248327855357)
  ·
    refine ⟨38112015329246343122945759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101632040877990248327855357 38112015329246343122945759)
    ·
      refine ⟨57168022993869514684418639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38112015329246343122945759 57168022993869514684418639)
      ·
        refine ⟨85752034490804272026627959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57168022993869514684418639 85752034490804272026627959)
        ·
          refine ⟨128628051736206408039941939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85752034490804272026627959 128628051736206408039941939)
          ·
            refine ⟨192942077604309612059912909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128628051736206408039941939 192942077604309612059912909)
            ·
              refine ⟨72353279101616104522467341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192942077604309612059912909 72353279101616104522467341)
              ·
                refine ⟨27132479663106039195925253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72353279101616104522467341 27132479663106039195925253)
                ·
                  refine ⟨5087339936832382349235985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27132479663106039195925253 5087339936832382349235985)
                  ·
                    refine ⟨3815504952624286761926989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087339936832382349235985 3815504952624286761926989)
                    ·
                      refine ⟨1430814357234107535722621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815504952624286761926989 1430814357234107535722621)
                      ·
                        rfl

theorem cell23_2786501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_2786501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786501 prefixEnd_2786501 := by exact prefixLift 2786501
  have htrace : WordTrace (prefixWord ++ tailWord_2786501) baseStart_2786501 baseEnd_2786501 := by
    simpa [prefixWord, tailWord_2786501, baseEnd_2786501] using wordTrace_append hprefix tailTrace_2786501
  have hstable : (prefixWord ++ tailWord_2786501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786501).length < 2 ^ (prefixWord ++ tailWord_2786501).sum := by decide
  have hdescent : baseEnd_2786501 < baseStart_2786501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786581 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2786581 : Nat := 118140960795 + 2786581 * 2 ^ 59
def prefixEnd_2786581 : Nat := 4983230072969 + 3 ^ 40 * 2786581 * 2
def baseEnd_2786581 : Nat := 476951811895489074240751

theorem tailTrace_2786581 : CollatzResearch.WordTrace tailWord_2786581 prefixEnd_2786581 476951811895489074240751 := by
  unfold tailWord_2786581
  simp only [CollatzResearch.WordTrace]
  refine ⟨101634958717700421990767597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67756639145133614660511731 101634958717700421990767597)
  ·
    refine ⟨38113109519137658246537849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101634958717700421990767597 38113109519137658246537849)
    ·
      refine ⟨28584832139353243684903387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38113109519137658246537849 28584832139353243684903387)
      ·
        refine ⟨42877248209029865527355081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28584832139353243684903387 42877248209029865527355081)
        ·
          refine ⟨32157936156772399145516311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42877248209029865527355081 32157936156772399145516311)
          ·
            refine ⟨48236904235158598718274467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32157936156772399145516311 48236904235158598718274467)
            ·
              refine ⟨72355356352737898077411701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48236904235158598718274467 72355356352737898077411701)
              ·
                refine ⟨6783314658069177944757347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72355356352737898077411701 6783314658069177944757347)
                ·
                  refine ⟨10174971987103766917136021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783314658069177944757347 10174971987103766917136021)
                  ·
                    refine ⟨476951811895489074240751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10174971987103766917136021 476951811895489074240751)
                    ·
                      rfl

theorem cell23_2786581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2786581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786581 prefixEnd_2786581 := by exact prefixLift 2786581
  have htrace : WordTrace (prefixWord ++ tailWord_2786581) baseStart_2786581 baseEnd_2786581 := by
    simpa [prefixWord, tailWord_2786581, baseEnd_2786581] using wordTrace_append hprefix tailTrace_2786581
  have hstable : (prefixWord ++ tailWord_2786581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786581).length < 2 ^ (prefixWord ++ tailWord_2786581).sum := by decide
  have hdescent : baseEnd_2786581 < baseStart_2786581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786588 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2786588 : Nat := 118140960795 + 2786588 * 2 ^ 59
def prefixEnd_2786588 : Nat := 4983230072969 + 3 ^ 40 * 2786588 * 2
def baseEnd_2786588 : Nat := 1430859030051048695334721

theorem tailTrace_2786588 : CollatzResearch.WordTrace tailWord_2786588 prefixEnd_2786588 1430859030051048695334721 := by
  unfold tailWord_2786588
  simp only [CollatzResearch.WordTrace]
  refine ⟨50817607014337531093136209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67756809352450041457514945 50817607014337531093136209)
  ·
    refine ⟨38113205260753148319852157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50817607014337531093136209 38113205260753148319852157)
    ·
      refine ⟨14292451972782430619944559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38113205260753148319852157 14292451972782430619944559)
      ·
        refine ⟨21438677959173645929916839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14292451972782430619944559 21438677959173645929916839)
        ·
          refine ⟨32158016938760468894875259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21438677959173645929916839 32158016938760468894875259)
          ·
            refine ⟨48237025408140703342312889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32158016938760468894875259 48237025408140703342312889)
            ·
              refine ⟨36177769056105527506734667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48237025408140703342312889 36177769056105527506734667)
              ·
                refine ⟨54266653584158291260102001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36177769056105527506734667 54266653584158291260102001)
                ·
                  refine ⟨40699990188118718445076501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54266653584158291260102001 40699990188118718445076501)
                  ·
                    refine ⟨1907812040068064927112961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40699990188118718445076501 1907812040068064927112961)
                    ·
                      refine ⟨1430859030051048695334721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907812040068064927112961 1430859030051048695334721)
                      ·
                        rfl

theorem cell23_2786588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2786588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786588 prefixEnd_2786588 := by exact prefixLift 2786588
  have htrace : WordTrace (prefixWord ++ tailWord_2786588) baseStart_2786588 baseEnd_2786588 := by
    simpa [prefixWord, tailWord_2786588, baseEnd_2786588] using wordTrace_append hprefix tailTrace_2786588
  have hstable : (prefixWord ++ tailWord_2786588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786588).length < 2 ^ (prefixWord ++ tailWord_2786588).sum := by decide
  have hdescent : baseEnd_2786588 < baseStart_2786588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786592 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2786592 : Nat := 118140960795 + 2786592 * 2 ^ 59
def prefixEnd_2786592 : Nat := 4983230072969 + 3 ^ 40 * 2786592 * 2
def baseEnd_2786592 : Nat := 1430861083973666679684703

theorem tailTrace_2786592 : CollatzResearch.WordTrace tailWord_2786592 prefixEnd_2786592 1430861083973666679684703 := by
  unfold tailWord_2786592
  simp only [CollatzResearch.WordTrace]
  refine ⟨50817679960330285434709015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67756906613773713912945353 50817679960330285434709015)
  ·
    refine ⟨76226519940495428152063523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50817679960330285434709015 76226519940495428152063523)
    ·
      refine ⟨114339779910743142228095285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76226519940495428152063523 114339779910743142228095285)
      ·
        refine ⟨10719354366632169583883933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114339779910743142228095285 10719354366632169583883933)
        ·
          refine ⟨4019757887487063593956475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10719354366632169583883933 4019757887487063593956475)
          ·
            refine ⟨6029636831230595390934713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019757887487063593956475 6029636831230595390934713)
            ·
              refine ⟨4522227623422946543201035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6029636831230595390934713 4522227623422946543201035)
              ·
                refine ⟨6783341435134419814801553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522227623422946543201035 6783341435134419814801553)
                ·
                  refine ⟨5087506076350814861101165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783341435134419814801553 5087506076350814861101165)
                  ·
                    refine ⟨1907814778631555572912937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5087506076350814861101165 1907814778631555572912937)
                    ·
                      refine ⟨1430861083973666679684703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907814778631555572912937 1430861083973666679684703)
                      ·
                        rfl

theorem cell23_2786592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2786592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786592 prefixEnd_2786592 := by exact prefixLift 2786592
  have htrace : WordTrace (prefixWord ++ tailWord_2786592) baseStart_2786592 baseEnd_2786592 := by
    simpa [prefixWord, tailWord_2786592, baseEnd_2786592] using wordTrace_append hprefix tailTrace_2786592
  have hstable : (prefixWord ++ tailWord_2786592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786592).length < 2 ^ (prefixWord ++ tailWord_2786592).sum := by decide
  have hdescent : baseEnd_2786592 < baseStart_2786592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786602 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2786602 : Nat := 118140960795 + 2786602 * 2 ^ 59
def prefixEnd_2786602 : Nat := 4983230072969 + 3 ^ 40 * 2786602 * 2
def baseEnd_2786602 : Nat := 476955406260070546853219

theorem tailTrace_2786602 : CollatzResearch.WordTrace tailWord_2786602 prefixEnd_2786602 476955406260070546853219 := by
  unfold tailWord_2786602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25408931162656085644320515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67757149767082895051521373 25408931162656085644320515)
  ·
    refine ⟨38113396743984128466480773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25408931162656085644320515 38113396743984128466480773)
    ·
      refine ⟨7146261889497024087465145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38113396743984128466480773 7146261889497024087465145)
      ·
        refine ⟨5359696417122768065598859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146261889497024087465145 5359696417122768065598859)
        ·
          refine ⟨8039544625684152098398289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359696417122768065598859 8039544625684152098398289)
          ·
            refine ⟨6029658469263114073798717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8039544625684152098398289 6029658469263114073798717)
            ·
              refine ⟨2261121925973667777674519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6029658469263114073798717 2261121925973667777674519)
              ·
                refine ⟨3391682888960501666511779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261121925973667777674519 3391682888960501666511779)
                ·
                  refine ⟨5087524333440752499767669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391682888960501666511779 5087524333440752499767669)
                  ·
                    refine ⟨476955406260070546853219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5087524333440752499767669 476955406260070546853219)
                    ·
                      rfl

theorem cell23_2786602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2786602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786602 prefixEnd_2786602 := by exact prefixLift 2786602
  have htrace : WordTrace (prefixWord ++ tailWord_2786602) baseStart_2786602 baseEnd_2786602 := by
    simpa [prefixWord, tailWord_2786602, baseEnd_2786602] using wordTrace_append hprefix tailTrace_2786602
  have hstable : (prefixWord ++ tailWord_2786602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786602).length < 2 ^ (prefixWord ++ tailWord_2786602).sum := by decide
  have hdescent : baseEnd_2786602 < baseStart_2786602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786622 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_2786622 : Nat := 118140960795 + 2786622 * 2 ^ 59
def prefixEnd_2786622 : Nat := 4983230072969 + 3 ^ 40 * 2786622 * 2
def baseEnd_2786622 : Nat := 1430876488393301562309565

theorem tailTrace_2786622 : CollatzResearch.WordTrace tailWord_2786622 prefixEnd_2786622 1430876488393301562309565 := by
  unfold tailWord_2786622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704556763818985749126265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67757636073701257328673413 12704556763818985749126265)
  ·
    refine ⟨9528417572864239311844699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12704556763818985749126265 9528417572864239311844699)
    ·
      refine ⟨14292626359296358967767049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9528417572864239311844699 14292626359296358967767049)
      ·
        refine ⟨10719469769472269225825287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14292626359296358967767049 10719469769472269225825287)
        ·
          refine ⟨16079204654208403838737931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10719469769472269225825287 16079204654208403838737931)
          ·
            refine ⟨24118806981312605758106897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079204654208403838737931 24118806981312605758106897)
            ·
              refine ⟨18089105235984454318580173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24118806981312605758106897 18089105235984454318580173)
              ·
                refine ⟨6783414463494170369467565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18089105235984454318580173 6783414463494170369467565)
                ·
                  refine ⟨2543780423810313888550337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6783414463494170369467565 2543780423810313888550337)
                  ·
                    refine ⟨1907835317857735416412753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543780423810313888550337 1907835317857735416412753)
                    ·
                      refine ⟨1430876488393301562309565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907835317857735416412753 1430876488393301562309565)
                      ·
                        rfl

theorem cell23_2786622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_2786622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786622 prefixEnd_2786622 := by exact prefixLift 2786622
  have htrace : WordTrace (prefixWord ++ tailWord_2786622) baseStart_2786622 baseEnd_2786622 := by
    simpa [prefixWord, tailWord_2786622, baseEnd_2786622] using wordTrace_append hprefix tailTrace_2786622
  have hstable : (prefixWord ++ tailWord_2786622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786622).length < 2 ^ (prefixWord ++ tailWord_2786622).sum := by decide
  have hdescent : baseEnd_2786622 < baseStart_2786622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786625 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2786625 : Nat := 118140960795 + 2786625 * 2 ^ 59
def prefixEnd_2786625 : Nat := 4983230072969 + 3 ^ 40 * 2786625 * 2
def baseEnd_2786625 : Nat := 1430878028835265050572051

theorem tailTrace_2786625 : CollatzResearch.WordTrace tailWord_2786625 prefixEnd_2786625 1430878028835265050572051 := by
  unfold tailWord_2786625
  simp only [CollatzResearch.WordTrace]
  refine ⟨101636563529541017505369329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67757709019694011670246219 101636563529541017505369329)
  ·
    refine ⟨76227422647155763129026997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101636563529541017505369329 76227422647155763129026997)
    ·
      refine ⟨7146320873170852793346281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76227422647155763129026997 7146320873170852793346281)
      ·
        refine ⟨5359740654878139595009711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146320873170852793346281 5359740654878139595009711)
        ·
          refine ⟨8039610982317209392514567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359740654878139595009711 8039610982317209392514567)
          ·
            refine ⟨12059416473475814088771851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039610982317209392514567 12059416473475814088771851)
            ·
              refine ⟨18089124710213721133157777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12059416473475814088771851 18089124710213721133157777)
              ·
                refine ⟨13566843532660290849868333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18089124710213721133157777 13566843532660290849868333)
                ·
                  refine ⟨5087566324747609068700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13566843532660290849868333 5087566324747609068700625)
                  ·
                    refine ⟨3815674743560706801525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5087566324747609068700625 3815674743560706801525469)
                    ·
                      refine ⟨1430878028835265050572051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815674743560706801525469 1430878028835265050572051)
                      ·
                        rfl

theorem cell23_2786625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2786625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786625 prefixEnd_2786625 := by exact prefixLift 2786625
  have htrace : WordTrace (prefixWord ++ tailWord_2786625) baseStart_2786625 baseEnd_2786625 := by
    simpa [prefixWord, tailWord_2786625, baseEnd_2786625] using wordTrace_append hprefix tailTrace_2786625
  have hstable : (prefixWord ++ tailWord_2786625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786625).length < 2 ^ (prefixWord ++ tailWord_2786625).sum := by decide
  have hdescent : baseEnd_2786625 < baseStart_2786625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786641 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2786641 : Nat := 118140960795 + 2786641 * 2 ^ 59
def prefixEnd_2786641 : Nat := 4983230072969 + 3 ^ 40 * 2786641 * 2
def baseEnd_2786641 : Nat := 476962081508578995990659

theorem tailTrace_2786641 : CollatzResearch.WordTrace tailWord_2786641 prefixEnd_2786641 476962081508578995990659 := by
  unfold tailWord_2786641
  simp only [CollatzResearch.WordTrace]
  refine ⟨101637147097483052237951777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67758098064988701491967851 101637147097483052237951777)
  ·
    refine ⟨76227860323112289178463833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101637147097483052237951777 76227860323112289178463833)
    ·
      refine ⟨57170895242334216883847875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76227860323112289178463833 57170895242334216883847875)
      ·
        refine ⟨85756342863501325325771813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57170895242334216883847875 85756342863501325325771813)
        ·
          refine ⟨16079314286906498498582215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85756342863501325325771813 16079314286906498498582215)
          ·
            refine ⟨24118971430359747747873323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079314286906498498582215 24118971430359747747873323)
            ·
              refine ⟨36178457145539621621809985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24118971430359747747873323 36178457145539621621809985)
              ·
                refine ⟨27133842859154716216357489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36178457145539621621809985 27133842859154716216357489)
                ·
                  refine ⟨20350382144366037162268117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27133842859154716216357489 20350382144366037162268117)
                  ·
                    refine ⟨476962081508578995990659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20350382144366037162268117 476962081508578995990659)
                    ·
                      rfl

theorem cell23_2786641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2786641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786641 prefixEnd_2786641 := by exact prefixLift 2786641
  have htrace : WordTrace (prefixWord ++ tailWord_2786641) baseStart_2786641 baseEnd_2786641 := by
    simpa [prefixWord, tailWord_2786641, baseEnd_2786641] using wordTrace_append hprefix tailTrace_2786641
  have hstable : (prefixWord ++ tailWord_2786641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786641).length < 2 ^ (prefixWord ++ tailWord_2786641).sum := by decide
  have hdescent : baseEnd_2786641 < baseStart_2786641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786653 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2786653 : Nat := 118140960795 + 2786653 * 2 ^ 59
def prefixEnd_2786653 : Nat := 4983230072969 + 3 ^ 40 * 2786653 * 2
def baseEnd_2786653 : Nat := 476964135431196980340641

theorem tailTrace_2786653 : CollatzResearch.WordTrace tailWord_2786653 prefixEnd_2786653 476964135431196980340641 := by
  unfold tailWord_2786653
  simp only [CollatzResearch.WordTrace]
  refine ⟨101637584773439578287388613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67758389848959718858259075 101637584773439578287388613)
  ·
    refine ⟨19057047145019920928885365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101637584773439578287388613 19057047145019920928885365)
    ·
      refine ⟨1786598169845617587083003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19057047145019920928885365 1786598169845617587083003)
      ·
        refine ⟨2679897254768426380624505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786598169845617587083003 2679897254768426380624505)
        ·
          refine ⟨2009922941076319785468379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679897254768426380624505 2009922941076319785468379)
          ·
            refine ⟨3014884411614479678202569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009922941076319785468379 3014884411614479678202569)
            ·
              refine ⟨2261163308710859758651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014884411614479678202569 2261163308710859758651927)
              ·
                refine ⟨3391744963066289637977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261163308710859758651927 3391744963066289637977891)
                ·
                  refine ⟨5087617444599434456966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391744963066289637977891 5087617444599434456966837)
                  ·
                    refine ⟨476964135431196980340641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5087617444599434456966837 476964135431196980340641)
                    ·
                      rfl

theorem cell23_2786653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2786653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786653 prefixEnd_2786653 := by exact prefixLift 2786653
  have htrace : WordTrace (prefixWord ++ tailWord_2786653) baseStart_2786653 baseEnd_2786653 := by
    simpa [prefixWord, tailWord_2786653, baseEnd_2786653] using wordTrace_append hprefix tailTrace_2786653
  have hstable : (prefixWord ++ tailWord_2786653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786653).length < 2 ^ (prefixWord ++ tailWord_2786653).sum := by decide
  have hdescent : baseEnd_2786653 < baseStart_2786653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786671 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 6]
def baseStart_2786671 : Nat := 118140960795 + 2786671 * 2 ^ 59
def prefixEnd_2786671 : Nat := 4983230072969 + 3 ^ 40 * 2786671 * 2
def baseEnd_2786671 : Nat := 476967216315123956865613

theorem tailTrace_2786671 : CollatzResearch.WordTrace tailWord_2786671 prefixEnd_2786671 476967216315123956865613 := by
  unfold tailWord_2786671
  simp only [CollatzResearch.WordTrace]
  refine ⟨101638241287374367361543867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67758827524916244907695911 101638241287374367361543867)
  ·
    refine ⟨152457361931061551042315801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101638241287374367361543867 152457361931061551042315801)
    ·
      refine ⟨114343021448296163281736851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152457361931061551042315801 114343021448296163281736851)
      ·
        refine ⟨171514532172444244922605277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114343021448296163281736851 171514532172444244922605277)
        ·
          refine ⟨64317949564666591845976979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171514532172444244922605277 64317949564666591845976979)
          ·
            refine ⟨96476924346999887768965469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64317949564666591845976979 96476924346999887768965469)
            ·
              refine ⟨36178846630124957913362051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96476924346999887768965469 36178846630124957913362051)
              ·
                refine ⟨54268269945187436870043077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36178846630124957913362051 54268269945187436870043077)
                ·
                  refine ⟨10175300614722644413133077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54268269945187436870043077 10175300614722644413133077)
                  ·
                    refine ⟨476967216315123956865613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10175300614722644413133077 476967216315123956865613)
                    ·
                      rfl

theorem cell23_2786671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_2786671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786671 prefixEnd_2786671 := by exact prefixLift 2786671
  have htrace : WordTrace (prefixWord ++ tailWord_2786671) baseStart_2786671 baseEnd_2786671 := by
    simpa [prefixWord, tailWord_2786671, baseEnd_2786671] using wordTrace_append hprefix tailTrace_2786671
  have hstable : (prefixWord ++ tailWord_2786671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786671).length < 2 ^ (prefixWord ++ tailWord_2786671).sum := by decide
  have hdescent : baseEnd_2786671 < baseStart_2786671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786686 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2786686 : Nat := 118140960795 + 2786686 * 2 ^ 59
def prefixEnd_2786686 : Nat := 4983230072969 + 3 ^ 40 * 2786686 * 2
def baseEnd_2786686 : Nat := 1430909351155189311909271

theorem tailTrace_2786686 : CollatzResearch.WordTrace tailWord_2786686 prefixEnd_2786686 1430909351155189311909271 := by
  unfold tailWord_2786686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704848547790003115417489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67759192254880016615559941 12704848547790003115417489)
  ·
    refine ⟨9528636410842502336563117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12704848547790003115417489 9528636410842502336563117)
    ·
      refine ⟨3573238654065938376211169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9528636410842502336563117 3573238654065938376211169)
      ·
        refine ⟨2679928990549453782158377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3573238654065938376211169 2679928990549453782158377)
        ·
          refine ⟨2009946742912090336618783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679928990549453782158377 2009946742912090336618783)
          ·
            refine ⟨3014920114368135504928175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009946742912090336618783 3014920114368135504928175)
            ·
              refine ⟨4522380171552203257392263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014920114368135504928175 4522380171552203257392263)
              ·
                refine ⟨6783570257328304886088395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522380171552203257392263 6783570257328304886088395)
                ·
                  refine ⟨10175355385992457329132593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783570257328304886088395 10175355385992457329132593)
                  ·
                    refine ⟨7631516539494342996849445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10175355385992457329132593 7631516539494342996849445)
                    ·
                      refine ⟨1430909351155189311909271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7631516539494342996849445 1430909351155189311909271)
                      ·
                        rfl

theorem cell23_2786686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2786686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786686 prefixEnd_2786686 := by exact prefixLift 2786686
  have htrace : WordTrace (prefixWord ++ tailWord_2786686) baseStart_2786686 baseEnd_2786686 := by
    simpa [prefixWord, tailWord_2786686, baseEnd_2786686] using wordTrace_append hprefix tailTrace_2786686
  have hstable : (prefixWord ++ tailWord_2786686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786686).length < 2 ^ (prefixWord ++ tailWord_2786686).sum := by decide
  have hdescent : baseEnd_2786686 < baseStart_2786686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786689 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_2786689 : Nat := 118140960795 + 2786689 * 2 ^ 59
def prefixEnd_2786689 : Nat := 4983230072969 + 3 ^ 40 * 2786689 * 2
def baseEnd_2786689 : Nat := 1430910891597152800171757

theorem tailTrace_2786689 : CollatzResearch.WordTrace tailWord_2786689 prefixEnd_2786689 1430910891597152800171757 := by
  unfold tailWord_2786689
  simp only [CollatzResearch.WordTrace]
  refine ⟨101638897801309156435699121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67759265200872770957132747 101638897801309156435699121)
  ·
    refine ⟨76229173350981867326774341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101638897801309156435699121 76229173350981867326774341)
    ·
      refine ⟨14292970003309100123770189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76229173350981867326774341 14292970003309100123770189)
      ·
        refine ⟨5359863751240912546413821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14292970003309100123770189 5359863751240912546413821)
        ·
          refine ⟨2009948906715342204905183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5359863751240912546413821 2009948906715342204905183)
          ·
            refine ⟨3014923360073013307357775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009948906715342204905183 3014923360073013307357775)
            ·
              refine ⟨4522385040109519961036663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014923360073013307357775 4522385040109519961036663)
              ·
                refine ⟨6783577560164279941554995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522385040109519961036663 6783577560164279941554995)
                ·
                  refine ⟨10175366340246419912332493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6783577560164279941554995 10175366340246419912332493)
                  ·
                    refine ⟨3815762377592407467124685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10175366340246419912332493 3815762377592407467124685)
                    ·
                      refine ⟨1430910891597152800171757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3815762377592407467124685 1430910891597152800171757)
                      ·
                        rfl

theorem cell23_2786689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_2786689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786689 prefixEnd_2786689 := by exact prefixLift 2786689
  have htrace : WordTrace (prefixWord ++ tailWord_2786689) baseStart_2786689 baseEnd_2786689 := by
    simpa [prefixWord, tailWord_2786689, baseEnd_2786689] using wordTrace_append hprefix tailTrace_2786689
  have hstable : (prefixWord ++ tailWord_2786689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786689).length < 2 ^ (prefixWord ++ tailWord_2786689).sum := by decide
  have hdescent : baseEnd_2786689 < baseStart_2786689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786768 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_2786768 : Nat := 118140960795 + 2786768 * 2 ^ 59
def prefixEnd_2786768 : Nat := 4983230072969 + 3 ^ 40 * 2786768 * 2
def baseEnd_2786768 : Nat := 1430951456568857991083893

theorem tailTrace_2786768 : CollatzResearch.WordTrace tailWord_2786768 prefixEnd_2786768 1430951456568857991083893 := by
  unfold tailWord_2786768
  simp only [CollatzResearch.WordTrace]
  refine ⟨50820889584011476463912479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67761186112015301951883305 50820889584011476463912479)
  ·
    refine ⟨76231334376017214695868719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50820889584011476463912479 76231334376017214695868719)
    ·
      refine ⟨114347001564025822043803079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76231334376017214695868719 114347001564025822043803079)
      ·
        refine ⟨171520502346038733065704619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114347001564025822043803079 171520502346038733065704619)
        ·
          refine ⟨257280753519058099598556929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171520502346038733065704619 257280753519058099598556929)
          ·
            refine ⟨192960565139293574698917697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257280753519058099598556929 192960565139293574698917697)
            ·
              refine ⟨144720423854470181024188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192960565139293574698917697 144720423854470181024188273)
              ·
                refine ⟨108540317890852635768141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144720423854470181024188273 108540317890852635768141205)
                ·
                  refine ⟨5087827401133717301631619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108540317890852635768141205 5087827401133717301631619)
                  ·
                    refine ⟨7631741101700575952447429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087827401133717301631619 7631741101700575952447429)
                    ·
                      refine ⟨1430951456568857991083893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7631741101700575952447429 1430951456568857991083893)
                      ·
                        rfl

theorem cell23_2786768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_2786768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786768 prefixEnd_2786768 := by exact prefixLift 2786768
  have htrace : WordTrace (prefixWord ++ tailWord_2786768) baseStart_2786768 baseEnd_2786768 := by
    simpa [prefixWord, tailWord_2786768, baseEnd_2786768] using wordTrace_append hprefix tailTrace_2786768
  have hstable : (prefixWord ++ tailWord_2786768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786768).length < 2 ^ (prefixWord ++ tailWord_2786768).sum := by decide
  have hdescent : baseEnd_2786768 < baseStart_2786768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786785 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_2786785 : Nat := 118140960795 + 2786785 * 2 ^ 59
def prefixEnd_2786785 : Nat := 4983230072969 + 3 ^ 40 * 2786785 * 2
def baseEnd_2786785 : Nat := 1430960185739984424571315

theorem tailTrace_2786785 : CollatzResearch.WordTrace tailWord_2786785 prefixEnd_2786785 1430960185739984424571315 := by
  unfold tailWord_2786785
  simp only [CollatzResearch.WordTrace]
  refine ⟨101642399208961364831193809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67761599472640909887462539 101642399208961364831193809)
  ·
    refine ⟨76231799406721023623395357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101642399208961364831193809 76231799406721023623395357)
    ·
      refine ⟨28586924777520383858773259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76231799406721023623395357 28586924777520383858773259)
      ·
        refine ⟨42880387166280575788159889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28586924777520383858773259 42880387166280575788159889)
        ·
          refine ⟨32160290374710431841119917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42880387166280575788159889 32160290374710431841119917)
          ·
            refine ⟨12060108890516411940419969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32160290374710431841119917 12060108890516411940419969)
            ·
              refine ⟨9045081667887308955314977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12060108890516411940419969 9045081667887308955314977)
              ·
                refine ⟨6783811250915481716486233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045081667887308955314977 6783811250915481716486233)
                ·
                  refine ⟨5087858438186611287364675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783811250915481716486233 5087858438186611287364675)
                  ·
                    refine ⟨7631787657279916931047013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087858438186611287364675 7631787657279916931047013)
                    ·
                      refine ⟨1430960185739984424571315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7631787657279916931047013 1430960185739984424571315)
                      ·
                        rfl

theorem cell23_2786785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_2786785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786785 prefixEnd_2786785 := by exact prefixLift 2786785
  have htrace : WordTrace (prefixWord ++ tailWord_2786785) baseStart_2786785 baseEnd_2786785 := by
    simpa [prefixWord, tailWord_2786785, baseEnd_2786785] using wordTrace_append hprefix tailTrace_2786785
  have hstable : (prefixWord ++ tailWord_2786785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786785).length < 2 ^ (prefixWord ++ tailWord_2786785).sum := by decide
  have hdescent : baseEnd_2786785 < baseStart_2786785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786802 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2786802 : Nat := 118140960795 + 2786802 * 2 ^ 59
def prefixEnd_2786802 : Nat := 4983230072969 + 3 ^ 40 * 2786802 * 2
def baseEnd_2786802 : Nat := 1430968914911110858058737

theorem tailTrace_2786802 : CollatzResearch.WordTrace tailWord_2786802 prefixEnd_2786802 1430968914911110858058737 := by
  unfold tailWord_2786802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25410754812474944183640665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67762012833266517823041773 25410754812474944183640665)
  ·
    refine ⟨19058066109356208137730499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25410754812474944183640665 19058066109356208137730499)
    ·
      refine ⟨28587099164034312206595749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058066109356208137730499 28587099164034312206595749)
      ·
        refine ⟨5360081093256433538736703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28587099164034312206595749 5360081093256433538736703)
        ·
          refine ⟨8040121639884650308105055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360081093256433538736703 8040121639884650308105055)
          ·
            refine ⟨12060182459826975462157583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040121639884650308105055 12060182459826975462157583)
            ·
              refine ⟨18090273689740463193236375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12060182459826975462157583 18090273689740463193236375)
              ·
                refine ⟨27135410534610694789854563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18090273689740463193236375 27135410534610694789854563)
                ·
                  refine ⟨40703115801916042184781845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27135410534610694789854563 40703115801916042184781845)
                  ·
                    refine ⟨1907958553214814477411649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40703115801916042184781845 1907958553214814477411649)
                    ·
                      refine ⟨1430968914911110858058737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1907958553214814477411649 1430968914911110858058737)
                      ·
                        rfl

theorem cell23_2786802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2786802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786802 prefixEnd_2786802 := by exact prefixLift 2786802
  have htrace : WordTrace (prefixWord ++ tailWord_2786802) baseStart_2786802 baseEnd_2786802 := by
    simpa [prefixWord, tailWord_2786802, baseEnd_2786802] using wordTrace_append hprefix tailTrace_2786802
  have hstable : (prefixWord ++ tailWord_2786802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786802).length < 2 ^ (prefixWord ++ tailWord_2786802).sum := by decide
  have hdescent : baseEnd_2786802 < baseStart_2786802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786872 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_2786872 : Nat := 118140960795 + 2786872 * 2 ^ 59
def prefixEnd_2786872 : Nat := 4983230072969 + 3 ^ 40 * 2786872 * 2
def baseEnd_2786872 : Nat := 477001619518975194727805

theorem tailTrace_2786872 : CollatzResearch.WordTrace tailWord_2786872 prefixEnd_2786872 477001619518975194727805 := by
  unfold tailWord_2786872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50822786179823089344805435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67763714906430785793073913 50822786179823089344805435)
  ·
    refine ⟨76234179269734634017208153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50822786179823089344805435 76234179269734634017208153)
    ·
      refine ⟨57175634452300975512906115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76234179269734634017208153 57175634452300975512906115)
      ·
        refine ⟨85763451678451463269359173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57175634452300975512906115 85763451678451463269359173)
        ·
          refine ⟨16080647189709649363004845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85763451678451463269359173 16080647189709649363004845)
          ·
            refine ⟨6030242696141118511126817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16080647189709649363004845 6030242696141118511126817)
            ·
              refine ⟨4522682022105838883345113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030242696141118511126817 4522682022105838883345113)
              ·
                refine ⟨3392011516579379162508835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522682022105838883345113 3392011516579379162508835)
                ·
                  refine ⟨5088017274869068743763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392011516579379162508835 5088017274869068743763253)
                  ·
                    refine ⟨477001619518975194727805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5088017274869068743763253 477001619518975194727805)
                    ·
                      rfl

theorem cell23_2786872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_2786872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786872 prefixEnd_2786872 := by exact prefixLift 2786872
  have htrace : WordTrace (prefixWord ++ tailWord_2786872) baseStart_2786872 baseEnd_2786872 := by
    simpa [prefixWord, tailWord_2786872, baseEnd_2786872] using wordTrace_append hprefix tailTrace_2786872
  have hstable : (prefixWord ++ tailWord_2786872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786872).length < 2 ^ (prefixWord ++ tailWord_2786872).sum := by decide
  have hdescent : baseEnd_2786872 < baseStart_2786872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786885 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2786885 : Nat := 118140960795 + 2786885 * 2 ^ 59
def prefixEnd_2786885 : Nat := 4983230072969 + 3 ^ 40 * 2786885 * 2
def baseEnd_2786885 : Nat := 477003844601811344440285

theorem tailTrace_2786885 : CollatzResearch.WordTrace tailWord_2786885 prefixEnd_2786885 477003844601811344440285 := by
  unfold tailWord_2786885
  simp only [CollatzResearch.WordTrace]
  refine ⟨101646046508599081909834109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67764031005732721273222739 101646046508599081909834109)
  ·
    refine ⟨38117267440724655716187791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101646046508599081909834109 38117267440724655716187791)
    ·
      refine ⟨57175901161086983574281687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38117267440724655716187791 57175901161086983574281687)
      ·
        refine ⟨85763851741630475361422531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57175901161086983574281687 85763851741630475361422531)
        ·
          refine ⟨128645777612445713042133797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85763851741630475361422531 128645777612445713042133797)
          ·
            refine ⟨24121083302333571195400087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128645777612445713042133797 24121083302333571195400087)
            ·
              refine ⟨36181624953500356793100131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24121083302333571195400087 36181624953500356793100131)
              ·
                refine ⟨54272437430250535189650197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36181624953500356793100131 54272437430250535189650197)
                ·
                  refine ⟨2544020504542993837014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54272437430250535189650197 2544020504542993837014853)
                  ·
                    refine ⟨477003844601811344440285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544020504542993837014853 477003844601811344440285)
                    ·
                      rfl

theorem cell23_2786885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2786885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786885 prefixEnd_2786885 := by exact prefixLift 2786885
  have htrace : WordTrace (prefixWord ++ tailWord_2786885) baseStart_2786885 baseEnd_2786885 := by
    simpa [prefixWord, tailWord_2786885, baseEnd_2786885] using wordTrace_append hprefix tailTrace_2786885
  have hstable : (prefixWord ++ tailWord_2786885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786885).length < 2 ^ (prefixWord ++ tailWord_2786885).sum := by decide
  have hdescent : baseEnd_2786885 < baseStart_2786885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786892 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2786892 : Nat := 118140960795 + 2786892 * 2 ^ 59
def prefixEnd_2786892 : Nat := 4983230072969 + 3 ^ 40 * 2786892 * 2
def baseEnd_2786892 : Nat := 1431015128170015505933323

theorem tailTrace_2786892 : CollatzResearch.WordTrace tailWord_2786892 prefixEnd_2786892 1431015128170015505933323 := by
  unfold tailWord_2786892
  simp only [CollatzResearch.WordTrace]
  refine ⟨50823150909786861052669465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67764201213049148070225953 50823150909786861052669465)
  ·
    refine ⟨38117363182340145789502099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50823150909786861052669465 38117363182340145789502099)
    ·
      refine ⟨57176044773510218684253149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38117363182340145789502099 57176044773510218684253149)
      ·
        refine ⟨21441016790066332006594931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57176044773510218684253149 21441016790066332006594931)
        ·
          refine ⟨32161525185099498009892397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441016790066332006594931 32161525185099498009892397)
          ·
            refine ⟨12060571944412311753709649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32161525185099498009892397 12060571944412311753709649)
            ·
              refine ⟨9045428958309233815282237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12060571944412311753709649 9045428958309233815282237)
              ·
                refine ⟨3392035859365962680730839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9045428958309233815282237 3392035859365962680730839)
                ·
                  refine ⟨5088053789048944021096259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392035859365962680730839 5088053789048944021096259)
                  ·
                    refine ⟨7632080683573416031644389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5088053789048944021096259 7632080683573416031644389)
                    ·
                      refine ⟨1431015128170015505933323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7632080683573416031644389 1431015128170015505933323)
                      ·
                        rfl

theorem cell23_2786892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2786892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786892 prefixEnd_2786892 := by exact prefixLift 2786892
  have htrace : WordTrace (prefixWord ++ tailWord_2786892) baseStart_2786892 baseEnd_2786892 := by
    simpa [prefixWord, tailWord_2786892, baseEnd_2786892] using wordTrace_append hprefix tailTrace_2786892
  have hstable : (prefixWord ++ tailWord_2786892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786892).length < 2 ^ (prefixWord ++ tailWord_2786892).sum := by decide
  have hdescent : baseEnd_2786892 < baseStart_2786892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786895 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_2786895 : Nat := 118140960795 + 2786895 * 2 ^ 59
def prefixEnd_2786895 : Nat := 4983230072969 + 3 ^ 40 * 2786895 * 2
def baseEnd_2786895 : Nat := 1431016668611978994195809

theorem tailTrace_2786895 : CollatzResearch.WordTrace tailWord_2786895 prefixEnd_2786895 1431016668611978994195809 := by
  unfold tailWord_2786895
  simp only [CollatzResearch.WordTrace]
  refine ⟨101646411238562853617698139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67764274159041902411798759 101646411238562853617698139)
  ·
    refine ⟨152469616857844280426547209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101646411238562853617698139 152469616857844280426547209)
    ·
      refine ⟨114352212643383210319910407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152469616857844280426547209 114352212643383210319910407)
      ·
        refine ⟨171528318965074815479865611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114352212643383210319910407 171528318965074815479865611)
        ·
          refine ⟨257292478447612223219798417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171528318965074815479865611 257292478447612223219798417)
          ·
            refine ⟨192969358835709167414848813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257292478447612223219798417 192969358835709167414848813)
            ·
              refine ⟨72363509563390937780568305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192969358835709167414848813 72363509563390937780568305)
              ·
                refine ⟨54272632172543203335426229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72363509563390937780568305 54272632172543203335426229)
                ·
                  refine ⟨5088059266175925312696209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54272632172543203335426229 5088059266175925312696209)
                  ·
                    refine ⟨3816044449631943984522157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5088059266175925312696209 3816044449631943984522157)
                    ·
                      refine ⟨1431016668611978994195809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816044449631943984522157 1431016668611978994195809)
                      ·
                        rfl

theorem cell23_2786895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_2786895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786895 prefixEnd_2786895 := by exact prefixLift 2786895
  have htrace : WordTrace (prefixWord ++ tailWord_2786895) baseStart_2786895 baseEnd_2786895 := by
    simpa [prefixWord, tailWord_2786895, baseEnd_2786895] using wordTrace_append hprefix tailTrace_2786895
  have hstable : (prefixWord ++ tailWord_2786895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786895).length < 2 ^ (prefixWord ++ tailWord_2786895).sum := by decide
  have hdescent : baseEnd_2786895 < baseStart_2786895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786915 : List Nat := [1, 1, 1, 5, 1, 4, 2, 8]
def baseStart_2786915 : Nat := 118140960795 + 2786915 * 2 ^ 59
def prefixEnd_2786915 : Nat := 4983230072969 + 3 ^ 40 * 2786915 * 2
def baseEnd_2786915 : Nat := 53000997712039589479471

theorem tailTrace_2786915 : CollatzResearch.WordTrace tailWord_2786915 prefixEnd_2786915 53000997712039589479471 := by
  unfold tailWord_2786915
  simp only [CollatzResearch.WordTrace]
  refine ⟨101647140698490397033426199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67764760465660264688950799 101647140698490397033426199)
  ·
    refine ⟨152470711047735595550139299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101647140698490397033426199 152470711047735595550139299)
    ·
      refine ⟨228706066571603393325208949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152470711047735595550139299 228706066571603393325208949)
      ·
        refine ⟨21441193741087818124238339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228706066571603393325208949 21441193741087818124238339)
        ·
          refine ⟨32161790611631727186357509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441193741087818124238339 32161790611631727186357509)
          ·
            refine ⟨6030335739680948847442033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32161790611631727186357509 6030335739680948847442033)
            ·
              refine ⟨4522751804760711635581525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030335739680948847442033 4522751804760711635581525)
              ·
                refine ⟨53000997712039589479471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4522751804760711635581525 53000997712039589479471)
                ·
                  rfl

theorem cell23_2786915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 8].length) (baseStart_2786915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786915 prefixEnd_2786915 := by exact prefixLift 2786915
  have htrace : WordTrace (prefixWord ++ tailWord_2786915) baseStart_2786915 baseEnd_2786915 := by
    simpa [prefixWord, tailWord_2786915, baseEnd_2786915] using wordTrace_append hprefix tailTrace_2786915
  have hstable : (prefixWord ++ tailWord_2786915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786915).length < 2 ^ (prefixWord ++ tailWord_2786915).sum := by decide
  have hdescent : baseEnd_2786915 < baseStart_2786915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786919 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 2, 4]
def baseStart_2786919 : Nat := 118140960795 + 2786919 * 2 ^ 59
def prefixEnd_2786919 : Nat := 4983230072969 + 3 ^ 40 * 2786919 * 2
def baseEnd_2786919 : Nat := 477009664049228966765233

theorem tailTrace_2786919 : CollatzResearch.WordTrace tailWord_2786919 prefixEnd_2786919 477009664049228966765233 := by
  unfold tailWord_2786919
  simp only [CollatzResearch.WordTrace]
  refine ⟨101647286590475905716571811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67764857726983937144381207 101647286590475905716571811)
  ·
    refine ⟨152470929885713858574857717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101647286590475905716571811 152470929885713858574857717)
    ·
      refine ⟨14294149676785674241392911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152470929885713858574857717 14294149676785674241392911)
      ·
        refine ⟨21441224515178511362089367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14294149676785674241392911 21441224515178511362089367)
        ·
          refine ⟨32161836772767767043134051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441224515178511362089367 32161836772767767043134051)
          ·
            refine ⟨48242755159151650564701077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32161836772767767043134051 48242755159151650564701077)
            ·
              refine ⟨2261379148085233620220363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48242755159151650564701077 2261379148085233620220363)
              ·
                refine ⟨3392068722127850430330545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261379148085233620220363 3392068722127850430330545)
                ·
                  refine ⟨2544051541595887822747909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392068722127850430330545 2544051541595887822747909)
                  ·
                    refine ⟨477009664049228966765233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544051541595887822747909 477009664049228966765233)
                    ·
                      rfl

theorem cell23_2786919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_2786919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786919 prefixEnd_2786919 := by exact prefixLift 2786919
  have htrace : WordTrace (prefixWord ++ tailWord_2786919) baseStart_2786919 baseEnd_2786919 := by
    simpa [prefixWord, tailWord_2786919, baseEnd_2786919] using wordTrace_append hprefix tailTrace_2786919
  have hstable : (prefixWord ++ tailWord_2786919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786919).length < 2 ^ (prefixWord ++ tailWord_2786919).sum := by decide
  have hdescent : baseEnd_2786919 < baseStart_2786919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786926 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2786926 : Nat := 118140960795 + 2786926 * 2 ^ 59
def prefixEnd_2786926 : Nat := 4983230072969 + 3 ^ 40 * 2786926 * 2
def baseEnd_2786926 : Nat := 1431032586512268372908167

theorem tailTrace_2786926 : CollatzResearch.WordTrace tailWord_2786926 prefixEnd_2786926 1431032586512268372908167 := by
  unfold tailWord_2786926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705942737681318239009579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67765027934300363941384421 12705942737681318239009579)
  ·
    refine ⟨19058914106521977358514369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705942737681318239009579 19058914106521977358514369)
    ·
      refine ⟨14294185579891483018885777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19058914106521977358514369 14294185579891483018885777)
      ·
        refine ⟨10720639184918612264164333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14294185579891483018885777 10720639184918612264164333)
        ·
          refine ⟨4020239694344479599061625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10720639184918612264164333 4020239694344479599061625)
          ·
            refine ⟨3015179770758359699296219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4020239694344479599061625 3015179770758359699296219)
            ·
              refine ⟨4522769656137539548944329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015179770758359699296219 4522769656137539548944329)
              ·
                refine ⟨3392077242103154661708247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522769656137539548944329 3392077242103154661708247)
                ·
                  refine ⟨5088115863154731992562371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392077242103154661708247 5088115863154731992562371)
                  ·
                    refine ⟨7632173794732097988843557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5088115863154731992562371 7632173794732097988843557)
                    ·
                      refine ⟨1431032586512268372908167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7632173794732097988843557 1431032586512268372908167)
                      ·
                        rfl

theorem cell23_2786926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2786926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786926 prefixEnd_2786926 := by exact prefixLift 2786926
  have htrace : WordTrace (prefixWord ++ tailWord_2786926) baseStart_2786926 baseEnd_2786926 := by
    simpa [prefixWord, tailWord_2786926, baseEnd_2786926] using wordTrace_append hprefix tailTrace_2786926
  have hstable : (prefixWord ++ tailWord_2786926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786926).length < 2 ^ (prefixWord ++ tailWord_2786926).sum := by decide
  have hdescent : baseEnd_2786926 < baseStart_2786926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786985 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_2786985 : Nat := 118140960795 + 2786985 * 2 ^ 59
def prefixEnd_2786985 : Nat := 4983230072969 + 3 ^ 40 * 2786985 * 2
def baseEnd_2786985 : Nat := 1431062881870883642070395

theorem tailTrace_2786985 : CollatzResearch.WordTrace tailWord_2786985 prefixEnd_2786985 1431062881870883642070395 := by
  unfold tailWord_2786985
  simp only [CollatzResearch.WordTrace]
  refine ⟨101649693808236798988474409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67766462538824532658982939 101649693808236798988474409)
  ·
    refine ⟨76237270356177599241355807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101649693808236798988474409 76237270356177599241355807)
    ·
      refine ⟨114355905534266398862033711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76237270356177599241355807 114355905534266398862033711)
      ·
        refine ⟨171533858301399598293050567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114355905534266398862033711 171533858301399598293050567)
        ·
          refine ⟨257300787452099397439575851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171533858301399598293050567 257300787452099397439575851)
          ·
            refine ⟨385951181178149096159363777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257300787452099397439575851 385951181178149096159363777)
            ·
              refine ⟨289463385883611822119522833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385951181178149096159363777 289463385883611822119522833)
              ·
                refine ⟨217097539412708866589642125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289463385883611822119522833 217097539412708866589642125)
                ·
                  refine ⟨81411577279765824971115797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217097539412708866589642125 81411577279765824971115797)
                  ·
                    refine ⟨3816167684989023045521053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81411577279765824971115797 3816167684989023045521053)
                    ·
                      refine ⟨1431062881870883642070395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816167684989023045521053 1431062881870883642070395)
                      ·
                        rfl

theorem cell23_2786985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_2786985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786985 prefixEnd_2786985 := by exact prefixLift 2786985
  have htrace : WordTrace (prefixWord ++ tailWord_2786985) baseStart_2786985 baseEnd_2786985 := by
    simpa [prefixWord, tailWord_2786985, baseEnd_2786985] using wordTrace_append hprefix tailTrace_2786985
  have hstable : (prefixWord ++ tailWord_2786985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786985).length < 2 ^ (prefixWord ++ tailWord_2786985).sum := by decide
  have hdescent : baseEnd_2786985 < baseStart_2786985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786995 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_2786995 : Nat := 118140960795 + 2786995 * 2 ^ 59
def prefixEnd_2786995 : Nat := 4983230072969 + 3 ^ 40 * 2786995 * 2
def baseEnd_2786995 : Nat := 1431068016677428602945349

theorem tailTrace_2786995 : CollatzResearch.WordTrace tailWord_2786995 prefixEnd_2786995 1431068016677428602945349 := by
  unfold tailWord_2786995
  simp only [CollatzResearch.WordTrace]
  refine ⟨101650058538200570696338439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67766705692133713797558959 101650058538200570696338439)
  ·
    refine ⟨152475087807300856044507659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101650058538200570696338439 152475087807300856044507659)
    ·
      refine ⟨228712631710951284066761489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152475087807300856044507659 228712631710951284066761489)
      ·
        refine ⟨171534473783213463050071117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228712631710951284066761489 171534473783213463050071117)
        ·
          refine ⟨64325427668705048643776669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171534473783213463050071117 64325427668705048643776669)
          ·
            refine ⟨24122035375764393241416251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64325427668705048643776669 24122035375764393241416251)
            ·
              refine ⟨36183053063646589862124377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122035375764393241416251 36183053063646589862124377)
              ·
                refine ⟨27137289797734942396593283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36183053063646589862124377 27137289797734942396593283)
                ·
                  refine ⟨40705934696602413594889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27137289797734942396593283 40705934696602413594889925)
                  ·
                    refine ⟨7632362755612952549041861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40705934696602413594889925 7632362755612952549041861)
                    ·
                      refine ⟨1431068016677428602945349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7632362755612952549041861 1431068016677428602945349)
                      ·
                        rfl

theorem cell23_2786995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_2786995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786995 prefixEnd_2786995 := by exact prefixLift 2786995
  have htrace : WordTrace (prefixWord ++ tailWord_2786995) baseStart_2786995 baseEnd_2786995 := by
    simpa [prefixWord, tailWord_2786995, baseEnd_2786995] using wordTrace_append hprefix tailTrace_2786995
  have hstable : (prefixWord ++ tailWord_2786995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786995).length < 2 ^ (prefixWord ++ tailWord_2786995).sum := by decide
  have hdescent : baseEnd_2786995 < baseStart_2786995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2786999 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_2786999 : Nat := 118140960795 + 2786999 * 2 ^ 59
def prefixEnd_2786999 : Nat := 4983230072969 + 3 ^ 40 * 2786999 * 2
def baseEnd_2786999 : Nat := 1431070070600046587295331

theorem tailTrace_2786999 : CollatzResearch.WordTrace tailWord_2786999 prefixEnd_2786999 1431070070600046587295331 := by
  unfold tailWord_2786999
  simp only [CollatzResearch.WordTrace]
  refine ⟨101650204430186079379484051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67766802953457386252989367 101650204430186079379484051)
  ·
    refine ⟨152475306645279119069226077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101650204430186079379484051 152475306645279119069226077)
    ·
      refine ⟨57178239991979669650959779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152475306645279119069226077 57178239991979669650959779)
      ·
        refine ⟨85767359987969504476439669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57178239991979669650959779 85767359987969504476439669)
        ·
          refine ⟨8040689998872141044666219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85767359987969504476439669 8040689998872141044666219)
          ·
            refine ⟨12061034998308211566999329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040689998872141044666219 12061034998308211566999329)
            ·
              refine ⟨9045776248731158675249497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12061034998308211566999329 9045776248731158675249497)
              ·
                refine ⟨6784332186548369006437123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045776248731158675249497 6784332186548369006437123)
                ·
                  refine ⟨10176498279822553509655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6784332186548369006437123 10176498279822553509655685)
                  ·
                    refine ⟨1908093427466728783060441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10176498279822553509655685 1908093427466728783060441)
                    ·
                      refine ⟨1431070070600046587295331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908093427466728783060441 1431070070600046587295331)
                      ·
                        rfl

theorem cell23_2786999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_2786999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2786999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2786999 prefixEnd_2786999 := by exact prefixLift 2786999
  have htrace : WordTrace (prefixWord ++ tailWord_2786999) baseStart_2786999 baseEnd_2786999 := by
    simpa [prefixWord, tailWord_2786999, baseEnd_2786999] using wordTrace_append hprefix tailTrace_2786999
  have hstable : (prefixWord ++ tailWord_2786999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2786999).length < 2 ^ (prefixWord ++ tailWord_2786999).sum := by decide
  have hdescent : baseEnd_2786999 < baseStart_2786999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2786999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787005 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 9]
def baseStart_2787005 : Nat := 118140960795 + 2787005 * 2 ^ 59
def prefixEnd_2787005 : Nat := 4983230072969 + 3 ^ 40 * 2787005 * 2
def baseEnd_2787005 : Nat := 159008127942663729313367

theorem tailTrace_2787005 : CollatzResearch.WordTrace tailWord_2787005 prefixEnd_2787005 159008127942663729313367 := by
  unfold tailWord_2787005
  simp only [CollatzResearch.WordTrace]
  refine ⟨101650423268164342404202469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67766948845442894936134979 101650423268164342404202469)
  ·
    refine ⟨19059454362780814200787963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101650423268164342404202469 19059454362780814200787963)
    ·
      refine ⟨28589181544171221301181945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19059454362780814200787963 28589181544171221301181945)
      ·
        refine ⟨21441886158128415975886459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28589181544171221301181945 21441886158128415975886459)
        ·
          refine ⟨32162829237192623963829689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441886158128415975886459 32162829237192623963829689)
          ·
            refine ⟨24122121927894467972872267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32162829237192623963829689 24122121927894467972872267)
            ·
              refine ⟨36183182891841701959308401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122121927894467972872267 36183182891841701959308401)
              ·
                refine ⟨27137387168881276469481301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36183182891841701959308401 27137387168881276469481301)
                ·
                  refine ⟨159008127942663729313367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27137387168881276469481301 159008127942663729313367)
                  ·
                    rfl

theorem cell23_2787005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_2787005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787005 prefixEnd_2787005 := by exact prefixLift 2787005
  have htrace : WordTrace (prefixWord ++ tailWord_2787005) baseStart_2787005 baseEnd_2787005 := by
    simpa [prefixWord, tailWord_2787005, baseEnd_2787005] using wordTrace_append hprefix tailTrace_2787005
  have hstable : (prefixWord ++ tailWord_2787005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787005).length < 2 ^ (prefixWord ++ tailWord_2787005).sum := by decide
  have hdescent : baseEnd_2787005 < baseStart_2787005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787010 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2787010 : Nat := 118140960795 + 2787010 * 2 ^ 59
def prefixEnd_2787010 : Nat := 4983230072969 + 3 ^ 40 * 2787010 * 2
def baseEnd_2787010 : Nat := 1431075718887246044257781

theorem tailTrace_2787010 : CollatzResearch.WordTrace tailWord_2787010 prefixEnd_2787010 1431075718887246044257781 := by
  unfold tailWord_2787010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25412651408286557064533621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67767070422097485505422989 25412651408286557064533621)
  ·
    refine ⟨2382436069526864724800027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25412651408286557064533621 2382436069526864724800027)
    ·
      refine ⟨3573654104290297087200041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382436069526864724800027 3573654104290297087200041)
      ·
        refine ⟨2680240578217722815400031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3573654104290297087200041 2680240578217722815400031)
        ·
          refine ⟨4020360867326584223100047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680240578217722815400031 4020360867326584223100047)
          ·
            refine ⟨6030541300989876334650071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020360867326584223100047 6030541300989876334650071)
            ·
              refine ⟨9045811951484814501975107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030541300989876334650071 9045811951484814501975107)
              ·
                refine ⟨13568717927227221752962661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9045811951484814501975107 13568717927227221752962661)
                ·
                  refine ⟨2544134611355104078680499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13568717927227221752962661 2544134611355104078680499)
                  ·
                    refine ⟨3816201917032656118020749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544134611355104078680499 3816201917032656118020749)
                    ·
                      refine ⟨1431075718887246044257781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816201917032656118020749 1431075718887246044257781)
                      ·
                        rfl

theorem cell23_2787010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2787010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787010 prefixEnd_2787010 := by exact prefixLift 2787010
  have htrace : WordTrace (prefixWord ++ tailWord_2787010) baseStart_2787010 baseEnd_2787010 := by
    simpa [prefixWord, tailWord_2787010, baseEnd_2787010] using wordTrace_append hprefix tailTrace_2787010
  have hstable : (prefixWord ++ tailWord_2787010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787010).length < 2 ^ (prefixWord ++ tailWord_2787010).sum := by decide
  have hdescent : baseEnd_2787010 < baseStart_2787010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787012 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2787012 : Nat := 118140960795 + 2787012 * 2 ^ 59
def prefixEnd_2787012 : Nat := 4983230072969 + 3 ^ 40 * 2787012 * 2
def baseEnd_2787012 : Nat := 1431076745848555036432771

theorem tailTrace_2787012 : CollatzResearch.WordTrace tailWord_2787012 prefixEnd_2787012 1431076745848555036432771 := by
  unfold tailWord_2787012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50825339289569491299853645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67767119052759321733138193 50825339289569491299853645)
  ·
    refine ⟨19059502233588559237445117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50825339289569491299853645 19059502233588559237445117)
    ·
      refine ⟨7147313337595709714041919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19059502233588559237445117 7147313337595709714041919)
      ·
        refine ⟨10720970006393564571062879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7147313337595709714041919 10720970006393564571062879)
        ·
          refine ⟨16081455009590346856594319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10720970006393564571062879 16081455009590346856594319)
          ·
            refine ⟨24122182514385520284891479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081455009590346856594319 24122182514385520284891479)
            ·
              refine ⟨36183273771578280427337219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122182514385520284891479 36183273771578280427337219)
              ·
                refine ⟨54274910657367420641005829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36183273771578280427337219 54274910657367420641005829)
                ·
                  refine ⟨10176545748256391370188593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54274910657367420641005829 10176545748256391370188593)
                  ·
                    refine ⟨7632409311192293527641445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10176545748256391370188593 7632409311192293527641445)
                    ·
                      refine ⟨1431076745848555036432771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7632409311192293527641445 1431076745848555036432771)
                      ·
                        rfl

theorem cell23_2787012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2787012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787012 prefixEnd_2787012 := by exact prefixLift 2787012
  have htrace : WordTrace (prefixWord ++ tailWord_2787012) baseStart_2787012 baseEnd_2787012 := by
    simpa [prefixWord, tailWord_2787012, baseEnd_2787012] using wordTrace_append hprefix tailTrace_2787012
  have hstable : (prefixWord ++ tailWord_2787012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787012).length < 2 ^ (prefixWord ++ tailWord_2787012).sum := by decide
  have hdescent : baseEnd_2787012 < baseStart_2787012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787022 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_2787022 : Nat := 118140960795 + 2787022 * 2 ^ 59
def prefixEnd_2787022 : Nat := 4983230072969 + 3 ^ 40 * 2787022 * 2
def baseEnd_2787022 : Nat := 159009097850566666367525

theorem tailTrace_2787022 : CollatzResearch.WordTrace tailWord_2787022 prefixEnd_2787022 159009097850566666367525 := by
  unfold tailWord_2787022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12706380413637844288446415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67767362206068502871714213 12706380413637844288446415)
  ·
    refine ⟨19059570620456766432669623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12706380413637844288446415 19059570620456766432669623)
    ·
      refine ⟨28589355930685149649004435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19059570620456766432669623 28589355930685149649004435)
      ·
        refine ⟨42884033896027724473506653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28589355930685149649004435 42884033896027724473506653)
        ·
          refine ⟨16081512711010396677564995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42884033896027724473506653 16081512711010396677564995)
          ·
            refine ⟨24122269066515595016347493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081512711010396677564995 24122269066515595016347493)
            ·
              refine ⟨4522925449971674065565155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24122269066515595016347493 4522925449971674065565155)
              ·
                refine ⟨6784388174957511098347733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522925449971674065565155 6784388174957511098347733)
                ·
                  refine ⟨159009097850566666367525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6784388174957511098347733 159009097850566666367525)
                  ·
                    rfl

theorem cell23_2787022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_2787022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787022 prefixEnd_2787022 := by exact prefixLift 2787022
  have htrace : WordTrace (prefixWord ++ tailWord_2787022) baseStart_2787022 baseEnd_2787022 := by
    simpa [prefixWord, tailWord_2787022, baseEnd_2787022] using wordTrace_append hprefix tailTrace_2787022
  have hstable : (prefixWord ++ tailWord_2787022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787022).length < 2 ^ (prefixWord ++ tailWord_2787022).sum := by decide
  have hdescent : baseEnd_2787022 < baseStart_2787022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787032 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2787032 : Nat := 118140960795 + 2787032 * 2 ^ 59
def prefixEnd_2787032 : Nat := 4983230072969 + 3 ^ 40 * 2787032 * 2
def baseEnd_2787032 : Nat := 1431087015461644958182679

theorem tailTrace_2787032 : CollatzResearch.WordTrace tailWord_2787032 prefixEnd_2787032 1431087015461644958182679 := by
  unfold tailWord_2787032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50825704019533263007717675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67767605359377684010290233 50825704019533263007717675)
  ·
    refine ⟨76238556029299894511576513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50825704019533263007717675 76238556029299894511576513)
    ·
      refine ⟨57178917021974920883682385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76238556029299894511576513 57178917021974920883682385)
      ·
        refine ⟨42884187766481190662761789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57178917021974920883682385 42884187766481190662761789)
        ·
          refine ⟨16081570412430446498535671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42884187766481190662761789 16081570412430446498535671)
          ·
            refine ⟨24122355618645669747803507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081570412430446498535671 24122355618645669747803507)
            ·
              refine ⟨36183533427968504621705261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122355618645669747803507 36183533427968504621705261)
              ·
                refine ⟨13568825035488189233139473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36183533427968504621705261 13568825035488189233139473)
                ·
                  refine ⟨10176618776616141924854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13568825035488189233139473 10176618776616141924854605)
                  ·
                    refine ⟨3816232041231053221820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10176618776616141924854605 3816232041231053221820477)
                    ·
                      refine ⟨1431087015461644958182679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816232041231053221820477 1431087015461644958182679)
                      ·
                        rfl

theorem cell23_2787032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2787032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787032 prefixEnd_2787032 := by exact prefixLift 2787032
  have htrace : WordTrace (prefixWord ++ tailWord_2787032) baseStart_2787032 baseEnd_2787032 := by
    simpa [prefixWord, tailWord_2787032, baseEnd_2787032] using wordTrace_append hprefix tailTrace_2787032
  have hstable : (prefixWord ++ tailWord_2787032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787032).length < 2 ^ (prefixWord ++ tailWord_2787032).sum := by decide
  have hdescent : baseEnd_2787032 < baseStart_2787032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787033 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 2, 2, 2]
def baseStart_2787033 : Nat := 118140960795 + 2787033 * 2 ^ 59
def prefixEnd_2787033 : Nat := 4983230072969 + 3 ^ 40 * 2787033 * 2
def baseEnd_2787033 : Nat := 1431087528942299454270175

theorem tailTrace_2787033 : CollatzResearch.WordTrace tailWord_2787033 prefixEnd_2787033 1431087528942299454270175 := by
  unfold tailWord_2787033
  simp only [CollatzResearch.WordTrace]
  refine ⟨101651444512062903186221753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67767629674708602124147835 101651444512062903186221753)
  ·
    refine ⟨76238583384047177389666315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101651444512062903186221753 76238583384047177389666315)
    ·
      refine ⟨114357875076070766084499473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76238583384047177389666315 114357875076070766084499473)
      ·
        refine ⟨85768406307053074563374605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114357875076070766084499473 85768406307053074563374605)
        ·
          refine ⟨32163152365144902961265477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85768406307053074563374605 32163152365144902961265477)
          ·
            refine ⟨6030591068464669305237277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32163152365144902961265477 6030591068464669305237277)
            ·
              refine ⟨2261471650674250989463979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6030591068464669305237277 2261471650674250989463979)
              ·
                refine ⟨3392207476011376484195969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261471650674250989463979 3392207476011376484195969)
                ·
                  refine ⟨2544155607008532363146977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392207476011376484195969 2544155607008532363146977)
                  ·
                    refine ⟨1908116705256399272360233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544155607008532363146977 1908116705256399272360233)
                    ·
                      refine ⟨1431087528942299454270175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908116705256399272360233 1431087528942299454270175)
                      ·
                        rfl

theorem cell23_2787033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_2787033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787033 prefixEnd_2787033 := by exact prefixLift 2787033
  have htrace : WordTrace (prefixWord ++ tailWord_2787033) baseStart_2787033 baseEnd_2787033 := by
    simpa [prefixWord, tailWord_2787033, baseEnd_2787033] using wordTrace_append hprefix tailTrace_2787033
  have hstable : (prefixWord ++ tailWord_2787033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787033).length < 2 ^ (prefixWord ++ tailWord_2787033).sum := by decide
  have hdescent : baseEnd_2787033 < baseStart_2787033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787072 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_2787072 : Nat := 118140960795 + 2787072 * 2 ^ 59
def prefixEnd_2787072 : Nat := 4983230072969 + 3 ^ 40 * 2787072 * 2
def baseEnd_2787072 : Nat := 1431107554687824801682495

theorem tailTrace_2787072 : CollatzResearch.WordTrace tailWord_2787072 prefixEnd_2787072 1431107554687824801682495 := by
  unfold tailWord_2787072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50826433479460806423445735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67768577972614408564594313 50826433479460806423445735)
  ·
    refine ⟨76239650219191209635168603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50826433479460806423445735 76239650219191209635168603)
    ·
      refine ⟨114359475328786814452752905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76239650219191209635168603 114359475328786814452752905)
      ·
        refine ⟨85769606496590110839564679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114359475328786814452752905 85769606496590110839564679)
        ·
          refine ⟨128654409744885166259347019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85769606496590110839564679 128654409744885166259347019)
          ·
            refine ⟨192981614617327749389020529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128654409744885166259347019 192981614617327749389020529)
            ·
              refine ⟨144736210962995812041765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192981614617327749389020529 144736210962995812041765397)
              ·
                refine ⟨6784509888890428689457753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144736210962995812041765397 6784509888890428689457753)
                ·
                  refine ⟨5088382416667821517093315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784509888890428689457753 5088382416667821517093315)
                  ·
                    refine ⟨7632573625001732275639973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5088382416667821517093315 7632573625001732275639973)
                    ·
                      refine ⟨1431107554687824801682495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7632573625001732275639973 1431107554687824801682495)
                      ·
                        rfl

theorem cell23_2787072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_2787072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787072 prefixEnd_2787072 := by exact prefixLift 2787072
  have htrace : WordTrace (prefixWord ++ tailWord_2787072) baseStart_2787072 baseEnd_2787072 := by
    simpa [prefixWord, tailWord_2787072, baseEnd_2787072] using wordTrace_append hprefix tailTrace_2787072
  have hstable : (prefixWord ++ tailWord_2787072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787072).length < 2 ^ (prefixWord ++ tailWord_2787072).sum := by decide
  have hdescent : baseEnd_2787072 < baseStart_2787072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787078 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2787078 : Nat := 118140960795 + 2787078 * 2 ^ 59
def prefixEnd_2787078 : Nat := 4983230072969 + 3 ^ 40 * 2787078 * 2
def baseEnd_2787078 : Nat := 1431110635571751778207469

theorem tailTrace_2787078 : CollatzResearch.WordTrace tailWord_2787078 prefixEnd_2787078 1431110635571751778207469 := by
  unfold tailWord_2787078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176658931153121120987809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67768723864599917247739925 3176658931153121120987809)
  ·
    refine ⟨2382494198364840840740857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3176658931153121120987809 2382494198364840840740857)
    ·
      refine ⟨1786870648773630630555643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2382494198364840840740857 1786870648773630630555643)
      ·
        refine ⟨2680305973160445945833465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786870648773630630555643 2680305973160445945833465)
        ·
          refine ⟨2010229479870334459375099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680305973160445945833465 2010229479870334459375099)
          ·
            refine ⟨3015344219805501689062649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010229479870334459375099 3015344219805501689062649)
            ·
              refine ⟨2261508164854126266796987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015344219805501689062649 2261508164854126266796987)
              ·
                refine ⟨3392262247281189400195481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261508164854126266796987 3392262247281189400195481)
                ·
                  refine ⟨2544196685460892050146611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392262247281189400195481 2544196685460892050146611)
                  ·
                    refine ⟨3816295028191338075219917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544196685460892050146611 3816295028191338075219917)
                    ·
                      refine ⟨1431110635571751778207469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816295028191338075219917 1431110635571751778207469)
                      ·
                        rfl

theorem cell23_2787078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2787078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787078 prefixEnd_2787078 := by exact prefixLift 2787078
  have htrace : WordTrace (prefixWord ++ tailWord_2787078) baseStart_2787078 baseEnd_2787078 := by
    simpa [prefixWord, tailWord_2787078, baseEnd_2787078] using wordTrace_append hprefix tailTrace_2787078
  have hstable : (prefixWord ++ tailWord_2787078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787078).length < 2 ^ (prefixWord ++ tailWord_2787078).sum := by decide
  have hdescent : baseEnd_2787078 < baseStart_2787078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787079 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2787079 : Nat := 118140960795 + 2787079 * 2 ^ 59
def prefixEnd_2787079 : Nat := 4983230072969 + 3 ^ 40 * 2787079 * 2
def baseEnd_2787079 : Nat := 1431111149052406274294963

theorem tailTrace_2787079 : CollatzResearch.WordTrace tailWord_2787079 prefixEnd_2787079 1431111149052406274294963 := by
  unfold tailWord_2787079
  simp only [CollatzResearch.WordTrace]
  refine ⟨101653122269896253042396291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67768748179930835361597527 101653122269896253042396291)
  ·
    refine ⟨152479683404844379563594437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101653122269896253042396291 152479683404844379563594437)
    ·
      refine ⟨28589940638408321168173957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152479683404844379563594437 28589940638408321168173957)
      ·
        refine ⟨5360613869701560219032617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28589940638408321168173957 5360613869701560219032617)
        ·
          refine ⟨4020460402276170164274463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5360613869701560219032617 4020460402276170164274463)
          ·
            refine ⟨6030690603414255246411695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020460402276170164274463 6030690603414255246411695)
            ·
              refine ⟨9046035905121382869617543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030690603414255246411695 9046035905121382869617543)
              ·
                refine ⟨13569053857682074304426315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9046035905121382869617543 13569053857682074304426315)
                ·
                  refine ⟨20353580786523111456639473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13569053857682074304426315 20353580786523111456639473)
                  ·
                    refine ⟨15265185589892333592479605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20353580786523111456639473 15265185589892333592479605)
                    ·
                      refine ⟨1431111149052406274294963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15265185589892333592479605 1431111149052406274294963)
                      ·
                        rfl

theorem cell23_2787079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2787079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787079 prefixEnd_2787079 := by exact prefixLift 2787079
  have htrace : WordTrace (prefixWord ++ tailWord_2787079) baseStart_2787079 baseEnd_2787079 := by
    simpa [prefixWord, tailWord_2787079, baseEnd_2787079] using wordTrace_append hprefix tailTrace_2787079
  have hstable : (prefixWord ++ tailWord_2787079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787079).length < 2 ^ (prefixWord ++ tailWord_2787079).sum := by decide
  have hdescent : baseEnd_2787079 < baseStart_2787079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787109 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_2787109 : Nat := 118140960795 + 2787109 * 2 ^ 59
def prefixEnd_2787109 : Nat := 4983230072969 + 3 ^ 40 * 2787109 * 2
def baseEnd_2787109 : Nat := 1431126553472041156919825

theorem tailTrace_2787109 : CollatzResearch.WordTrace tailWord_2787109 prefixEnd_2787109 1431126553472041156919825 := by
  unfold tailWord_2787109
  simp only [CollatzResearch.WordTrace]
  refine ⟨101654216459787568165988381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67769477639858378777325587 101654216459787568165988381)
  ·
    refine ⟨38120331172420338062245643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101654216459787568165988381 38120331172420338062245643)
    ·
      refine ⟨57180496758630507093368465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38120331172420338062245643 57180496758630507093368465)
      ·
        refine ⟨42885372568972880320026349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57180496758630507093368465 42885372568972880320026349)
        ·
          refine ⟨16082014713364830120009881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42885372568972880320026349 16082014713364830120009881)
          ·
            refine ⟨12061511035023622590007411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16082014713364830120009881 12061511035023622590007411)
            ·
              refine ⟨18092266552535433885011117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12061511035023622590007411 18092266552535433885011117)
              ·
                refine ⟨6784599957200787706879169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18092266552535433885011117 6784599957200787706879169)
                ·
                  refine ⟨5088449967900590780159377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784599957200787706879169 5088449967900590780159377)
                  ·
                    refine ⟨3816337475925443085119533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5088449967900590780159377 3816337475925443085119533)
                    ·
                      refine ⟨1431126553472041156919825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816337475925443085119533 1431126553472041156919825)
                      ·
                        rfl

theorem cell23_2787109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_2787109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787109 prefixEnd_2787109 := by exact prefixLift 2787109
  have htrace : WordTrace (prefixWord ++ tailWord_2787109) baseStart_2787109 baseEnd_2787109 := by
    simpa [prefixWord, tailWord_2787109, baseEnd_2787109] using wordTrace_append hprefix tailTrace_2787109
  have hstable : (prefixWord ++ tailWord_2787109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787109).length < 2 ^ (prefixWord ++ tailWord_2787109).sum := by decide
  have hdescent : baseEnd_2787109 < baseStart_2787109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787133 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2787133 : Nat := 118140960795 + 2787133 * 2 ^ 59
def prefixEnd_2787133 : Nat := 4983230072969 + 3 ^ 40 * 2787133 * 2
def baseEnd_2787133 : Nat := 477046292335916354339905

theorem tailTrace_2787133 : CollatzResearch.WordTrace tailWord_2787133 prefixEnd_2787133 477046292335916354339905 := by
  unfold tailWord_2787133
  simp only [CollatzResearch.WordTrace]
  refine ⟨101655091811700620264862053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67770061207800413509908035 101655091811700620264862053)
  ·
    refine ⟨19060329714693866299661635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101655091811700620264862053 19060329714693866299661635)
    ·
      refine ⟨28590494572040799449492453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19060329714693866299661635 28590494572040799449492453)
      ·
        refine ⟨5360717732257649896779835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28590494572040799449492453 5360717732257649896779835)
        ·
          refine ⟨8041076598386474845169753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360717732257649896779835 8041076598386474845169753)
          ·
            refine ⟨6030807448789856133877315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8041076598386474845169753 6030807448789856133877315)
            ·
              refine ⟨9046211173184784200815973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030807448789856133877315 9046211173184784200815973)
              ·
                refine ⟨1696164594972147037652995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9046211173184784200815973 1696164594972147037652995)
                ·
                  refine ⟨2544246892458220556479493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696164594972147037652995 2544246892458220556479493)
                  ·
                    refine ⟨477046292335916354339905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544246892458220556479493 477046292335916354339905)
                    ·
                      rfl

theorem cell23_2787133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2787133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787133 prefixEnd_2787133 := by exact prefixLift 2787133
  have htrace : WordTrace (prefixWord ++ tailWord_2787133) baseStart_2787133 baseEnd_2787133 := by
    simpa [prefixWord, tailWord_2787133, baseEnd_2787133] using wordTrace_append hprefix tailTrace_2787133
  have hstable : (prefixWord ++ tailWord_2787133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787133).length < 2 ^ (prefixWord ++ tailWord_2787133).sum := by decide
  have hdescent : baseEnd_2787133 < baseStart_2787133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787156 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2787156 : Nat := 118140960795 + 2787156 * 2 ^ 59
def prefixEnd_2787156 : Nat := 4983230072969 + 3 ^ 40 * 2787156 * 2
def baseEnd_2787156 : Nat := 1431150687062802473032109

theorem tailTrace_2787156 : CollatzResearch.WordTrace tailWord_2787156 prefixEnd_2787156 1431150687062802473032109 := by
  unfold tailWord_2787156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50827965345308647596474661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67770620460411530128632881 50827965345308647596474661)
  ·
    refine ⟨9530243502245371424338999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50827965345308647596474661 9530243502245371424338999)
    ·
      refine ⟨14295365253368057136508499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9530243502245371424338999 14295365253368057136508499)
      ·
        refine ⟨21443047880052085704762749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14295365253368057136508499 21443047880052085704762749)
        ·
          refine ⟨8041142955019532139286031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21443047880052085704762749 8041142955019532139286031)
          ·
            refine ⟨12061714432529298208929047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041142955019532139286031 12061714432529298208929047)
            ·
              refine ⟨18092571648793947313393571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12061714432529298208929047 18092571648793947313393571)
              ·
                refine ⟨27138857473190920970090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18092571648793947313393571 27138857473190920970090357)
                ·
                  refine ⟨2544267888111648840945971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27138857473190920970090357 2544267888111648840945971)
                  ·
                    refine ⟨3816401832167473261418957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544267888111648840945971 3816401832167473261418957)
                    ·
                      refine ⟨1431150687062802473032109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816401832167473261418957 1431150687062802473032109)
                      ·
                        rfl

theorem cell23_2787156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2787156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787156 prefixEnd_2787156 := by exact prefixLift 2787156
  have htrace : WordTrace (prefixWord ++ tailWord_2787156) baseStart_2787156 baseEnd_2787156 := by
    simpa [prefixWord, tailWord_2787156, baseEnd_2787156] using wordTrace_append hprefix tailTrace_2787156
  have hstable : (prefixWord ++ tailWord_2787156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787156).length < 2 ^ (prefixWord ++ tailWord_2787156).sum := by decide
  have hdescent : baseEnd_2787156 < baseStart_2787156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787190 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2787190 : Nat := 118140960795 + 2787190 * 2 ^ 59
def prefixEnd_2787190 : Nat := 4983230072969 + 3 ^ 40 * 2787190 * 2
def baseEnd_2787190 : Nat := 1431168145405055340006953

theorem tailTrace_2787190 : CollatzResearch.WordTrace tailWord_2787190 prefixEnd_2787190 1431168145405055340006953 := by
  unfold tailWord_2787190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353573173280882437480439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67771447181662745999791349 6353573173280882437480439)
  ·
    refine ⟨9530359759921323656220659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6353573173280882437480439 9530359759921323656220659)
    ·
      refine ⟨14295539639881985484330989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9530359759921323656220659 14295539639881985484330989)
      ·
        refine ⟨5360827364955744556624121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14295539639881985484330989 5360827364955744556624121)
        ·
          refine ⟨4020620523716808417468091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5360827364955744556624121 4020620523716808417468091)
          ·
            refine ⟨6030930785575212626202137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020620523716808417468091 6030930785575212626202137)
            ·
              refine ⟨4523198089181409469651603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030930785575212626202137 4523198089181409469651603)
              ·
                refine ⟨6784797133772114204477405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523198089181409469651603 6784797133772114204477405)
                ·
                  refine ⟨2544298925164542826679027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6784797133772114204477405 2544298925164542826679027)
                  ·
                    refine ⟨3816448387746814240018541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544298925164542826679027 3816448387746814240018541)
                    ·
                      refine ⟨1431168145405055340006953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816448387746814240018541 1431168145405055340006953)
                      ·
                        rfl

theorem cell23_2787190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2787190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787190 prefixEnd_2787190 := by exact prefixLift 2787190
  have htrace : WordTrace (prefixWord ++ tailWord_2787190) baseStart_2787190 baseEnd_2787190 := by
    simpa [prefixWord, tailWord_2787190, baseEnd_2787190] using wordTrace_append hprefix tailTrace_2787190
  have hstable : (prefixWord ++ tailWord_2787190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787190).length < 2 ^ (prefixWord ++ tailWord_2787190).sum := by decide
  have hdescent : baseEnd_2787190 < baseStart_2787190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787224 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2787224 : Nat := 118140960795 + 2787224 * 2 ^ 59
def prefixEnd_2787224 : Nat := 4983230072969 + 3 ^ 40 * 2787224 * 2
def baseEnd_2787224 : Nat := 1431185603747308206981797

theorem tailTrace_2787224 : CollatzResearch.WordTrace tailWord_2787224 prefixEnd_2787224 1431185603747308206981797 := by
  unfold tailWord_2787224
  simp only [CollatzResearch.WordTrace]
  refine ⟨50829205427185471403212363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67772273902913961870949817 50829205427185471403212363)
  ·
    refine ⟨76243808140778207104818545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50829205427185471403212363 76243808140778207104818545)
    ·
      refine ⟨57182856105583655328613909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76243808140778207104818545 57182856105583655328613909)
      ·
        refine ⟨2680446379949233843528777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57182856105583655328613909 2680446379949233843528777)
        ·
          refine ⟨2010334784961925382646583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680446379949233843528777 2010334784961925382646583)
          ·
            refine ⟨3015502177442888073969875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010334784961925382646583 3015502177442888073969875)
            ·
              refine ⟨4523253266164332110954813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015502177442888073969875 4523253266164332110954813)
              ·
                refine ⟨1696219974811624541608055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4523253266164332110954813 1696219974811624541608055)
                ·
                  refine ⟨2544329962217436812412083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696219974811624541608055 2544329962217436812412083)
                  ·
                    refine ⟨3816494943326155218618125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544329962217436812412083 3816494943326155218618125)
                    ·
                      refine ⟨1431185603747308206981797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816494943326155218618125 1431185603747308206981797)
                      ·
                        rfl

theorem cell23_2787224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2787224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787224 prefixEnd_2787224 := by exact prefixLift 2787224
  have htrace : WordTrace (prefixWord ++ tailWord_2787224) baseStart_2787224 baseEnd_2787224 := by
    simpa [prefixWord, tailWord_2787224, baseEnd_2787224] using wordTrace_append hprefix tailTrace_2787224
  have hstable : (prefixWord ++ tailWord_2787224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787224).length < 2 ^ (prefixWord ++ tailWord_2787224).sum := by decide
  have hdescent : baseEnd_2787224 < baseStart_2787224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787232 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_2787232 : Nat := 118140960795 + 2787232 * 2 ^ 59
def prefixEnd_2787232 : Nat := 4983230072969 + 3 ^ 40 * 2787232 * 2
def baseEnd_2787232 : Nat := 477063237197514725227253

theorem tailTrace_2787232 : CollatzResearch.WordTrace tailWord_2787232 prefixEnd_2787232 477063237197514725227253 := by
  unfold tailWord_2787232
  simp only [CollatzResearch.WordTrace]
  refine ⟨50829351319170980086357975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67772468425561306781810633 50829351319170980086357975)
  ·
    refine ⟨76244026978756470129536963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50829351319170980086357975 76244026978756470129536963)
    ·
      refine ⟨114366040468134705194305445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76244026978756470129536963 114366040468134705194305445)
      ·
        refine ⟨21443632587775257223932271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114366040468134705194305445 21443632587775257223932271)
        ·
          refine ⟨32165448881662885835898407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21443632587775257223932271 32165448881662885835898407)
          ·
            refine ⟨48248173322494328753847611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32165448881662885835898407 48248173322494328753847611)
            ·
              refine ⟨72372259983741493130771417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48248173322494328753847611 72372259983741493130771417)
              ·
                refine ⟨54279194987806119848078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72372259983741493130771417 54279194987806119848078563)
                ·
                  refine ⟨81418792481709179772117845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54279194987806119848078563 81418792481709179772117845)
                  ·
                    refine ⟨477063237197514725227253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81418792481709179772117845 477063237197514725227253)
                    ·
                      rfl

theorem cell23_2787232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_2787232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787232 prefixEnd_2787232 := by exact prefixLift 2787232
  have htrace : WordTrace (prefixWord ++ tailWord_2787232) baseStart_2787232 baseEnd_2787232 := by
    simpa [prefixWord, tailWord_2787232, baseEnd_2787232] using wordTrace_append hprefix tailTrace_2787232
  have hstable : (prefixWord ++ tailWord_2787232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787232).length < 2 ^ (prefixWord ++ tailWord_2787232).sum := by decide
  have hdescent : baseEnd_2787232 < baseStart_2787232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787256 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_2787256 : Nat := 118140960795 + 2787256 * 2 ^ 59
def prefixEnd_2787256 : Nat := 4983230072969 + 3 ^ 40 * 2787256 * 2
def baseEnd_2787256 : Nat := 1431202035128252081781649

theorem tailTrace_2787256 : CollatzResearch.WordTrace tailWord_2787256 prefixEnd_2787256 1431202035128252081781649 := by
  unfold tailWord_2787256
  simp only [CollatzResearch.WordTrace]
  refine ⟨50829788995127506135794811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67773051993503341514393081 50829788995127506135794811)
  ·
    refine ⟨76244683492691259203692217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50829788995127506135794811 76244683492691259203692217)
    ·
      refine ⟨57183512619518444402769163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76244683492691259203692217 57183512619518444402769163)
      ·
        refine ⟨85775268929277666604153745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57183512619518444402769163 85775268929277666604153745)
        ·
          refine ⟨64331451696958249953115309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85775268929277666604153745 64331451696958249953115309)
          ·
            refine ⟨24124294386359343732418241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64331451696958249953115309 24124294386359343732418241)
            ·
              refine ⟨18093220789769507799313681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24124294386359343732418241 18093220789769507799313681)
              ·
                refine ⟨13569915592327130849485261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18093220789769507799313681 13569915592327130849485261)
                ·
                  refine ⟨5088718347122674068556973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13569915592327130849485261 5088718347122674068556973)
                  ·
                    refine ⟨1908269380171002775708865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5088718347122674068556973 1908269380171002775708865)
                    ·
                      refine ⟨1431202035128252081781649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908269380171002775708865 1431202035128252081781649)
                      ·
                        rfl

theorem cell23_2787256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_2787256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787256 prefixEnd_2787256 := by exact prefixLift 2787256
  have htrace : WordTrace (prefixWord ++ tailWord_2787256) baseStart_2787256 baseEnd_2787256 := by
    simpa [prefixWord, tailWord_2787256, baseEnd_2787256] using wordTrace_append hprefix tailTrace_2787256
  have hstable : (prefixWord ++ tailWord_2787256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787256).length < 2 ^ (prefixWord ++ tailWord_2787256).sum := by decide
  have hdescent : baseEnd_2787256 < baseStart_2787256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787298 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2787298 : Nat := 118140960795 + 2787298 * 2 ^ 59
def prefixEnd_2787298 : Nat := 4983230072969 + 3 ^ 40 * 2787298 * 2
def baseEnd_2787298 : Nat := 1431223601315740917456457

theorem tailTrace_2787298 : CollatzResearch.WordTrace tailWord_2787298 prefixEnd_2787298 1431223601315740917456457 := by
  unfold tailWord_2787298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25415277464025713361154637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67774073237401902296412365 25415277464025713361154637)
  ·
    refine ⟨9530729049009642510432989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25415277464025713361154637 9530729049009642510432989)
    ·
      refine ⟨3574023393378615941412371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9530729049009642510432989 3574023393378615941412371)
      ·
        refine ⟨5361035090067923912118557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574023393378615941412371 5361035090067923912118557)
        ·
          refine ⟨2010388158775471467044459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5361035090067923912118557 2010388158775471467044459)
          ·
            refine ⟨3015582238163207200566689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010388158775471467044459 3015582238163207200566689)
            ·
              refine ⟨2261686678622405400425017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015582238163207200566689 2261686678622405400425017)
              ·
                refine ⟨1696265008966804050318763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261686678622405400425017 1696265008966804050318763)
                ·
                  refine ⟨2544397513450206075478145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696265008966804050318763 2544397513450206075478145)
                  ·
                    refine ⟨1908298135087654556608609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544397513450206075478145 1908298135087654556608609)
                    ·
                      refine ⟨1431223601315740917456457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908298135087654556608609 1431223601315740917456457)
                      ·
                        rfl

theorem cell23_2787298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2787298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787298 prefixEnd_2787298 := by exact prefixLift 2787298
  have htrace : WordTrace (prefixWord ++ tailWord_2787298) baseStart_2787298 baseEnd_2787298 := by
    simpa [prefixWord, tailWord_2787298, baseEnd_2787298] using wordTrace_append hprefix tailTrace_2787298
  have hstable : (prefixWord ++ tailWord_2787298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787298).length < 2 ^ (prefixWord ++ tailWord_2787298).sum := by decide
  have hdescent : baseEnd_2787298 < baseStart_2787298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787326 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2787326 : Nat := 118140960795 + 2787326 * 2 ^ 59
def prefixEnd_2787326 : Nat := 4983230072969 + 3 ^ 40 * 2787326 * 2
def baseEnd_2787326 : Nat := 159026442086007423100703

theorem tailTrace_2787326 : CollatzResearch.WordTrace tailWord_2787326 prefixEnd_2787326 159026442086007423100703 := by
  unfold tailWord_2787326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707766387500176778329729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67774754066667609484425221 12707766387500176778329729)
  ·
    refine ⟨9530824790625132583747297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12707766387500176778329729 9530824790625132583747297)
    ·
      refine ⟨7148118592968849437810473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9530824790625132583747297 7148118592968849437810473)
      ·
        refine ⟨5361088944726637078357855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148118592968849437810473 5361088944726637078357855)
        ·
          refine ⟨8041633417089955617536783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361088944726637078357855 8041633417089955617536783)
          ·
            refine ⟨12062450125634933426305175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041633417089955617536783 12062450125634933426305175)
            ·
              refine ⟨18093675188452400139457763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12062450125634933426305175 18093675188452400139457763)
              ·
                refine ⟨27140512782678600209186645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18093675188452400139457763 27140512782678600209186645)
                ·
                  refine ⟨159026442086007423100703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27140512782678600209186645 159026442086007423100703)
                  ·
                    rfl

theorem cell23_2787326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2787326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787326 prefixEnd_2787326 := by exact prefixLift 2787326
  have htrace : WordTrace (prefixWord ++ tailWord_2787326) baseStart_2787326 baseEnd_2787326 := by
    simpa [prefixWord, tailWord_2787326, baseEnd_2787326] using wordTrace_append hprefix tailTrace_2787326
  have hstable : (prefixWord ++ tailWord_2787326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787326).length < 2 ^ (prefixWord ++ tailWord_2787326).sum := by decide
  have hdescent : baseEnd_2787326 < baseStart_2787326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787339 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 7]
def baseStart_2787339 : Nat := 118140960795 + 2787339 * 2 ^ 59
def prefixEnd_2787339 : Nat := 4983230072969 + 3 ^ 40 * 2787339 * 2
def baseEnd_2787339 : Nat := 477081551340858419014589

theorem tailTrace_2787339 : CollatzResearch.WordTrace tailWord_2787339 prefixEnd_2787339 477081551340858419014589 := by
  unfold tailWord_2787339
  simp only [CollatzResearch.WordTrace]
  refine ⟨101662605248954317446861071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67775070165969544964574047 101662605248954317446861071)
  ·
    refine ⟨152493907873431476170291607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101662605248954317446861071 152493907873431476170291607)
    ·
      refine ⟨228740861810147214255437411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152493907873431476170291607 228740861810147214255437411)
      ·
        refine ⟨343111292715220821383156117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228740861810147214255437411 343111292715220821383156117)
        ·
          refine ⟨16083341846025976002335443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 343111292715220821383156117 16083341846025976002335443)
          ·
            refine ⟨24125012769038964003503165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16083341846025976002335443 24125012769038964003503165)
            ·
              refine ⟨9046879788389611501313687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24125012769038964003503165 9046879788389611501313687)
              ·
                refine ⟨13570319682584417251970531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9046879788389611501313687 13570319682584417251970531)
                ·
                  refine ⟨20355479523876625877955797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13570319682584417251970531 20355479523876625877955797)
                  ·
                    refine ⟨477081551340858419014589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20355479523876625877955797 477081551340858419014589)
                    ·
                      rfl

theorem cell23_2787339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_2787339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787339 prefixEnd_2787339 := by exact prefixLift 2787339
  have htrace : WordTrace (prefixWord ++ tailWord_2787339) baseStart_2787339 baseEnd_2787339 := by
    simpa [prefixWord, tailWord_2787339, baseEnd_2787339] using wordTrace_append hprefix tailTrace_2787339
  have hstable : (prefixWord ++ tailWord_2787339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787339).length < 2 ^ (prefixWord ++ tailWord_2787339).sum := by decide
  have hdescent : baseEnd_2787339 < baseStart_2787339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787399 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 10]
def baseStart_2787399 : Nat := 118140960795 + 2787399 * 2 ^ 59
def prefixEnd_2787399 : Nat := 4983230072969 + 3 ^ 40 * 2787399 * 2
def baseEnd_2787399 : Nat := 159030606984649446921499

theorem tailTrace_2787399 : CollatzResearch.WordTrace tailWord_2787399 prefixEnd_2787399 159030606984649446921499 := by
  unfold tailWord_2787399
  simp only [CollatzResearch.WordTrace]
  refine ⟨101664793628736947694045251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67776529085824631796030167 101664793628736947694045251)
  ·
    refine ⟨152497190443105421541067877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101664793628736947694045251 152497190443105421541067877)
    ·
      refine ⟨28593223208082266538950227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152497190443105421541067877 28593223208082266538950227)
      ·
        refine ⟨42889834812123399808425341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28593223208082266538950227 42889834812123399808425341)
        ·
          refine ⟨16083688054546274928159503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42889834812123399808425341 16083688054546274928159503)
          ·
            refine ⟨24125532081819412392239255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16083688054546274928159503 24125532081819412392239255)
            ·
              refine ⟨36188298122729118588358883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24125532081819412392239255 36188298122729118588358883)
              ·
                refine ⟨54282447184093677882538325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36188298122729118588358883 54282447184093677882538325)
                ·
                  refine ⟨159030606984649446921499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54282447184093677882538325 159030606984649446921499)
                  ·
                    rfl

theorem cell23_2787399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 10].length) (baseStart_2787399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787399 prefixEnd_2787399 := by exact prefixLift 2787399
  have htrace : WordTrace (prefixWord ++ tailWord_2787399) baseStart_2787399 baseEnd_2787399 := by
    simpa [prefixWord, tailWord_2787399, baseEnd_2787399] using wordTrace_append hprefix tailTrace_2787399
  have hstable : (prefixWord ++ tailWord_2787399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787399).length < 2 ^ (prefixWord ++ tailWord_2787399).sum := by decide
  have hdescent : baseEnd_2787399 < baseStart_2787399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787413 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2787413 : Nat := 118140960795 + 2787413 * 2 ^ 59
def prefixEnd_2787413 : Nat := 4983230072969 + 3 ^ 40 * 2787413 * 2
def baseEnd_2787413 : Nat := 1431282651591007967518427

theorem tailTrace_2787413 : CollatzResearch.WordTrace tailWord_2787413 prefixEnd_2787413 1431282651591007967518427 := by
  unfold tailWord_2787413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101665304250686228085054893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67776869500457485390036595 101665304250686228085054893)
  ·
    refine ⟨38124489094007335531895585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101665304250686228085054893 38124489094007335531895585)
    ·
      refine ⟨28593366820505501648921689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38124489094007335531895585 28593366820505501648921689)
      ·
        refine ⟨21445025115379126236691267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28593366820505501648921689 21445025115379126236691267)
        ·
          refine ⟨32167537673068689355036901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21445025115379126236691267 32167537673068689355036901)
          ·
            refine ⟨6031413313700379254069419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32167537673068689355036901 6031413313700379254069419)
            ·
              refine ⟨9047119970550568881104129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031413313700379254069419 9047119970550568881104129)
              ·
                refine ⟨6785339977912926660828097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9047119970550568881104129 6785339977912926660828097)
                ·
                  refine ⟨5089004983434694995621073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6785339977912926660828097 5089004983434694995621073)
                  ·
                    refine ⟨3816753737576021246715805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089004983434694995621073 3816753737576021246715805)
                    ·
                      refine ⟨1431282651591007967518427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816753737576021246715805 1431282651591007967518427)
                      ·
                        rfl

theorem cell23_2787413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2787413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787413 prefixEnd_2787413 := by exact prefixLift 2787413
  have htrace : WordTrace (prefixWord ++ tailWord_2787413) baseStart_2787413 baseEnd_2787413 := by
    simpa [prefixWord, tailWord_2787413, baseEnd_2787413] using wordTrace_append hprefix tailTrace_2787413
  have hstable : (prefixWord ++ tailWord_2787413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787413).length < 2 ^ (prefixWord ++ tailWord_2787413).sum := by decide
  have hdescent : baseEnd_2787413 < baseStart_2787413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787420 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2787420 : Nat := 118140960795 + 2787420 * 2 ^ 59
def prefixEnd_2787420 : Nat := 4983230072969 + 3 ^ 40 * 2787420 * 2
def baseEnd_2787420 : Nat := 477095415318529813376965

theorem tailTrace_2787420 : CollatzResearch.WordTrace tailWord_2787420 prefixEnd_2787420 477095415318529813376965 := by
  unfold tailWord_2787420
  simp only [CollatzResearch.WordTrace]
  refine ⟨50832779780830434140279857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67777039707773912187039809 50832779780830434140279857)
  ·
    refine ⟨38124584835622825605209893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50832779780830434140279857 38124584835622825605209893)
    ·
      refine ⟨7148359656679279800976855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38124584835622825605209893 7148359656679279800976855)
      ·
        refine ⟨10722539485018919701465283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148359656679279800976855 10722539485018919701465283)
        ·
          refine ⟨16083809227528379552197925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10722539485018919701465283 16083809227528379552197925)
          ·
            refine ⟨3015714230161571166037111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16083809227528379552197925 3015714230161571166037111)
            ·
              refine ⟨4523571345242356749055667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015714230161571166037111 4523571345242356749055667)
              ·
                refine ⟨6785357017863535123583501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523571345242356749055667 6785357017863535123583501)
                ·
                  refine ⟨2544508881698825671343813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6785357017863535123583501 2544508881698825671343813)
                  ·
                    refine ⟨477095415318529813376965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544508881698825671343813 477095415318529813376965)
                    ·
                      rfl

theorem cell23_2787420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2787420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787420 prefixEnd_2787420 := by exact prefixLift 2787420
  have htrace : WordTrace (prefixWord ++ tailWord_2787420) baseStart_2787420 baseEnd_2787420 := by
    simpa [prefixWord, tailWord_2787420, baseEnd_2787420] using wordTrace_append hprefix tailTrace_2787420
  have hstable : (prefixWord ++ tailWord_2787420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787420).length < 2 ^ (prefixWord ++ tailWord_2787420).sum := by decide
  have hdescent : baseEnd_2787420 < baseStart_2787420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787493 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_2787493 : Nat := 118140960795 + 2787493 * 2 ^ 59
def prefixEnd_2787493 : Nat := 4983230072969 + 3 ^ 40 * 2787493 * 2
def baseEnd_2787493 : Nat := 477107910014455884839353

theorem tailTrace_2787493 : CollatzResearch.WordTrace tailWord_2787493 prefixEnd_2787493 477107910014455884839353 := by
  unfold tailWord_2787493
  simp only [CollatzResearch.WordTrace]
  refine ⟨101668222090396401747967133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67778814726930934498644755 101668222090396401747967133)
  ·
    refine ⟨38125583283898650655487675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101668222090396401747967133 38125583283898650655487675)
    ·
      refine ⟨57188374925847975983231513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38125583283898650655487675 57188374925847975983231513)
      ·
        refine ⟨42891281194385981987423635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57188374925847975983231513 42891281194385981987423635)
        ·
          refine ⟨64336921791578972981135453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42891281194385981987423635 64336921791578972981135453)
          ·
            refine ⟨24126345671842114867925795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64336921791578972981135453 24126345671842114867925795)
            ·
              refine ⟨36189518507763172301888693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24126345671842114867925795 36189518507763172301888693)
              ·
                refine ⟨3392767360102797403302065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36189518507763172301888693 3392767360102797403302065)
                ·
                  refine ⟨2544575520077098052476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392767360102797403302065 2544575520077098052476549)
                  ·
                    refine ⟨477107910014455884839353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544575520077098052476549 477107910014455884839353)
                    ·
                      rfl

theorem cell23_2787493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_2787493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787493 prefixEnd_2787493 := by exact prefixLift 2787493
  have htrace : WordTrace (prefixWord ++ tailWord_2787493) baseStart_2787493 baseEnd_2787493 := by
    simpa [prefixWord, tailWord_2787493, baseEnd_2787493] using wordTrace_append hprefix tailTrace_2787493
  have hstable : (prefixWord ++ tailWord_2787493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787493).length < 2 ^ (prefixWord ++ tailWord_2787493).sum := by decide
  have hdescent : baseEnd_2787493 < baseStart_2787493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787503 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_2787503 : Nat := 118140960795 + 2787503 * 2 ^ 59
def prefixEnd_2787503 : Nat := 4983230072969 + 3 ^ 40 * 2787503 * 2
def baseEnd_2787503 : Nat := 1431328864849912615393013

theorem tailTrace_2787503 : CollatzResearch.WordTrace tailWord_2787503 prefixEnd_2787503 1431328864849912615393013 := by
  unfold tailWord_2787503
  simp only [CollatzResearch.WordTrace]
  refine ⟨101668586820360173455831163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67779057880240115637220775 101668586820360173455831163)
  ·
    refine ⟨152502880230540260183746745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101668586820360173455831163 152502880230540260183746745)
    ·
      refine ⟨114377160172905195137810059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152502880230540260183746745 114377160172905195137810059)
      ·
        refine ⟨171565740259357792706715089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114377160172905195137810059 171565740259357792706715089)
        ·
          refine ⟨128674305194518344530036317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171565740259357792706715089 128674305194518344530036317)
          ·
            refine ⟨48252864447944379198763619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128674305194518344530036317 48252864447944379198763619)
            ·
              refine ⟨72379296671916568798145429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48252864447944379198763619 72379296671916568798145429)
              ·
                refine ⟨3392779531496089162413067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72379296671916568798145429 3392779531496089162413067)
                ·
                  refine ⟨5089169297244133743619601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392779531496089162413067 5089169297244133743619601)
                  ·
                    refine ⟨3816876972933100307714701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089169297244133743619601 3816876972933100307714701)
                    ·
                      refine ⟨1431328864849912615393013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816876972933100307714701 1431328864849912615393013)
                      ·
                        rfl

theorem cell23_2787503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_2787503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787503 prefixEnd_2787503 := by exact prefixLift 2787503
  have htrace : WordTrace (prefixWord ++ tailWord_2787503) baseStart_2787503 baseEnd_2787503 := by
    simpa [prefixWord, tailWord_2787503, baseEnd_2787503] using wordTrace_append hprefix tailTrace_2787503
  have hstable : (prefixWord ++ tailWord_2787503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787503).length < 2 ^ (prefixWord ++ tailWord_2787503).sum := by decide
  have hdescent : baseEnd_2787503 < baseStart_2787503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787520 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_2787520 : Nat := 118140960795 + 2787520 * 2 ^ 59
def prefixEnd_2787520 : Nat := 4983230072969 + 3 ^ 40 * 2787520 * 2
def baseEnd_2787520 : Nat := 1431337594021039048880435

theorem tailTrace_2787520 : CollatzResearch.WordTrace tailWord_2787520 prefixEnd_2787520 1431337594021039048880435 := by
  unfold tailWord_2787520
  simp only [CollatzResearch.WordTrace]
  refine ⟨50834603430649292679600007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67779471240865723572800009 50834603430649292679600007)
  ·
    refine ⟨76251905145973939019400011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50834603430649292679600007 76251905145973939019400011)
    ·
      refine ⟨114377857718960908529100017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76251905145973939019400011 114377857718960908529100017)
      ·
        refine ⟨85783393289220681396825013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114377857718960908529100017 85783393289220681396825013)
        ·
          refine ⟨8042193120864438880952345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85783393289220681396825013 8042193120864438880952345)
          ·
            refine ⟨6031644840648329160714259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8042193120864438880952345 6031644840648329160714259)
            ·
              refine ⟨9047467260972493741071389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031644840648329160714259 9047467260972493741071389)
              ·
                refine ⟨3392800222864685152901771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9047467260972493741071389 3392800222864685152901771)
                ·
                  refine ⟨5089200334297027729352657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392800222864685152901771 5089200334297027729352657)
                  ·
                    refine ⟨3816900250722770797014493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089200334297027729352657 3816900250722770797014493)
                    ·
                      refine ⟨1431337594021039048880435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3816900250722770797014493 1431337594021039048880435)
                      ·
                        rfl

theorem cell23_2787520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_2787520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787520 prefixEnd_2787520 := by exact prefixLift 2787520
  have htrace : WordTrace (prefixWord ++ tailWord_2787520) baseStart_2787520 baseEnd_2787520 := by
    simpa [prefixWord, tailWord_2787520, baseEnd_2787520] using wordTrace_append hprefix tailTrace_2787520
  have hstable : (prefixWord ++ tailWord_2787520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787520).length < 2 ^ (prefixWord ++ tailWord_2787520).sum := by decide
  have hdescent : baseEnd_2787520 < baseStart_2787520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787534 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_2787534 : Nat := 118140960795 + 2787534 * 2 ^ 59
def prefixEnd_2787534 : Nat := 4983230072969 + 3 ^ 40 * 2787534 * 2
def baseEnd_2787534 : Nat := 1431344782750201994105371

theorem tailTrace_2787534 : CollatzResearch.WordTrace tailWord_2787534 prefixEnd_2787534 1431344782750201994105371 := by
  unfold tailWord_2787534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708714685405983218776207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67779811655498577166806437 12708714685405983218776207)
  ·
    refine ⟨19063072028108974828164311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12708714685405983218776207 19063072028108974828164311)
    ·
      refine ⟨28594608042163462242246467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063072028108974828164311 28594608042163462242246467)
      ·
        refine ⟨42891912063245193363369701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28594608042163462242246467 42891912063245193363369701)
        ·
          refine ⟨8042233511858473755631819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42891912063245193363369701 8042233511858473755631819)
          ·
            refine ⟨12063350267787710633447729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8042233511858473755631819 12063350267787710633447729)
            ·
              refine ⟨9047512700840782975085797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12063350267787710633447729 9047512700840782975085797)
              ·
                refine ⟨1696408631407646807828587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9047512700840782975085797 1696408631407646807828587)
                ·
                  refine ⟨2544612947111470211742881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696408631407646807828587 2544612947111470211742881)
                  ·
                    refine ⟨1908459710333602658807161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544612947111470211742881 1908459710333602658807161)
                    ·
                      refine ⟨1431344782750201994105371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908459710333602658807161 1431344782750201994105371)
                      ·
                        rfl

theorem cell23_2787534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_2787534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787534 prefixEnd_2787534 := by exact prefixLift 2787534
  have htrace : WordTrace (prefixWord ++ tailWord_2787534) baseStart_2787534 baseEnd_2787534 := by
    simpa [prefixWord, tailWord_2787534, baseEnd_2787534] using wordTrace_append hprefix tailTrace_2787534
  have hstable : (prefixWord ++ tailWord_2787534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787534).length < 2 ^ (prefixWord ++ tailWord_2787534).sum := by decide
  have hdescent : baseEnd_2787534 < baseStart_2787534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787680 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_2787680 : Nat := 118140960795 + 2787680 * 2 ^ 59
def prefixEnd_2787680 : Nat := 4983230072969 + 3 ^ 40 * 2787680 * 2
def baseEnd_2787680 : Nat := 1431419750925758422879699

theorem tailTrace_2787680 : CollatzResearch.WordTrace tailWord_2787680 prefixEnd_2787680 1431419750925758422879699 := by
  unfold tailWord_2787680
  simp only [CollatzResearch.WordTrace]
  refine ⟨50837521270359466342512247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67783361693812621790016329 50837521270359466342512247)
  ·
    refine ⟨76256281905539199513768371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50837521270359466342512247 76256281905539199513768371)
    ·
      refine ⟨114384422858308799270652557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76256281905539199513768371 114384422858308799270652557)
      ·
        refine ⟨42894158571865799726494709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114384422858308799270652557 42894158571865799726494709)
        ·
          refine ⟨4021327366112418724358879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42894158571865799726494709 4021327366112418724358879)
          ·
            refine ⟨6031991049168628086538319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021327366112418724358879 6031991049168628086538319)
            ·
              refine ⟨9047986573752942129807479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031991049168628086538319 9047986573752942129807479)
              ·
                refine ⟨13571979860629413194711219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047986573752942129807479 13571979860629413194711219)
                ·
                  refine ⟨20357969790944119792066829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571979860629413194711219 20357969790944119792066829)
                  ·
                    refine ⟨7634238671604044922025061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20357969790944119792066829 7634238671604044922025061)
                    ·
                      refine ⟨1431419750925758422879699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7634238671604044922025061 1431419750925758422879699)
                      ·
                        rfl

theorem cell23_2787680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_2787680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787680 prefixEnd_2787680 := by exact prefixLift 2787680
  have htrace : WordTrace (prefixWord ++ tailWord_2787680) baseStart_2787680 baseEnd_2787680 := by
    simpa [prefixWord, tailWord_2787680, baseEnd_2787680] using wordTrace_append hprefix tailTrace_2787680
  have hstable : (prefixWord ++ tailWord_2787680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787680).length < 2 ^ (prefixWord ++ tailWord_2787680).sum := by decide
  have hdescent : baseEnd_2787680 < baseStart_2787680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787693 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2787693 : Nat := 118140960795 + 2787693 * 2 ^ 59
def prefixEnd_2787693 : Nat := 4983230072969 + 3 ^ 40 * 2787693 * 2
def baseEnd_2787693 : Nat := 1431426426174266872017139

theorem tailTrace_2787693 : CollatzResearch.WordTrace tailWord_2787693 prefixEnd_2787693 1431426426174266872017139 := by
  unfold tailWord_2787693
  simp only [CollatzResearch.WordTrace]
  refine ⟨101675516689671835905247733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67783677793114557270165155 101675516689671835905247733)
  ·
    refine ⟨9532079689656734616116975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101675516689671835905247733 9532079689656734616116975)
    ·
      refine ⟨14298119534485101924175463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9532079689656734616116975 14298119534485101924175463)
      ·
        refine ⟨21447179301727652886263195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298119534485101924175463 21447179301727652886263195)
        ·
          refine ⟨32170768952591479329394793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21447179301727652886263195 32170768952591479329394793)
          ·
            refine ⟨24128076714443609497046095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32170768952591479329394793 24128076714443609497046095)
            ·
              refine ⟨36192115071665414245569143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24128076714443609497046095 36192115071665414245569143)
              ·
                refine ⟨54288172607498121368353715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36192115071665414245569143 54288172607498121368353715)
                ·
                  refine ⟨81432258911247182052530573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54288172607498121368353715 81432258911247182052530573)
                  ·
                    refine ⟨30537097091717693269698965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81432258911247182052530573 30537097091717693269698965)
                    ·
                      refine ⟨1431426426174266872017139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30537097091717693269698965 1431426426174266872017139)
                      ·
                        rfl

theorem cell23_2787693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2787693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787693 prefixEnd_2787693 := by exact prefixLift 2787693
  have htrace : WordTrace (prefixWord ++ tailWord_2787693) baseStart_2787693 baseEnd_2787693 := by
    simpa [prefixWord, tailWord_2787693, baseEnd_2787693] using wordTrace_append hprefix tailTrace_2787693
  have hstable : (prefixWord ++ tailWord_2787693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787693).length < 2 ^ (prefixWord ++ tailWord_2787693).sum := by decide
  have hdescent : baseEnd_2787693 < baseStart_2787693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787703 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 6]
def baseStart_2787703 : Nat := 118140960795 + 2787703 * 2 ^ 59
def prefixEnd_2787703 : Nat := 4983230072969 + 3 ^ 40 * 2787703 * 2
def baseEnd_2787703 : Nat := 159047951220090203654677

theorem tailTrace_2787703 : CollatzResearch.WordTrace tailWord_2787703 prefixEnd_2787703 159047951220090203654677 := by
  unfold tailWord_2787703
  simp only [CollatzResearch.WordTrace]
  refine ⟨101675881419635607613111763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67783920946423738408741175 101675881419635607613111763)
  ·
    refine ⟨152513822129453411419667645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101675881419635607613111763 152513822129453411419667645)
    ·
      refine ⟨57192683298545029282375367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152513822129453411419667645 57192683298545029282375367)
      ·
        refine ⟨85789024947817543923563051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57192683298545029282375367 85789024947817543923563051)
        ·
          refine ⟨128683537421726315885344577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85789024947817543923563051 128683537421726315885344577)
          ·
            refine ⟨96512653066294736914008433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128683537421726315885344577 96512653066294736914008433)
            ·
              refine ⟨72384489799721052685506325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96512653066294736914008433 72384489799721052685506325)
              ·
                refine ⟨3393022959361924344633109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72384489799721052685506325 3393022959361924344633109)
                ·
                  refine ⟨159047951220090203654677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3393022959361924344633109 159047951220090203654677)
                  ·
                    rfl

theorem cell23_2787703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 6].length) (baseStart_2787703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787703 prefixEnd_2787703 := by exact prefixLift 2787703
  have htrace : WordTrace (prefixWord ++ tailWord_2787703) baseStart_2787703 baseEnd_2787703 := by
    simpa [prefixWord, tailWord_2787703, baseEnd_2787703] using wordTrace_append hprefix tailTrace_2787703
  have hstable : (prefixWord ++ tailWord_2787703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787703).length < 2 ^ (prefixWord ++ tailWord_2787703).sum := by decide
  have hdescent : baseEnd_2787703 < baseStart_2787703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787707 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 1, 4]
def baseStart_2787707 : Nat := 118140960795 + 2787707 * 2 ^ 59
def prefixEnd_2787707 : Nat := 4983230072969 + 3 ^ 40 * 2787707 * 2
def baseEnd_2787707 : Nat := 477144538301143272414025

theorem tailTrace_2787707 : CollatzResearch.WordTrace tailWord_2787707 prefixEnd_2787707 477144538301143272414025 := by
  unfold tailWord_2787707
  simp only [CollatzResearch.WordTrace]
  refine ⟨101676027311621116296257375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67784018207747410864171583 101676027311621116296257375)
  ·
    refine ⟨152514040967431674444386063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101676027311621116296257375 152514040967431674444386063)
    ·
      refine ⟨228771061451147511666579095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152514040967431674444386063 228771061451147511666579095)
      ·
        refine ⟨343156592176721267499868643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228771061451147511666579095 343156592176721267499868643)
        ·
          refine ⟨514734888265081901249802965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343156592176721267499868643 514734888265081901249802965)
          ·
            refine ⟨12064098943712857060542257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 514734888265081901249802965 12064098943712857060542257)
            ·
              refine ⟨9048074207784642795406693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12064098943712857060542257 9048074207784642795406693)
              ·
                refine ⟨1696513913959620524138755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9048074207784642795406693 1696513913959620524138755)
                ·
                  refine ⟨2544770870939430786208133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696513913959620524138755 2544770870939430786208133)
                  ·
                    refine ⟨477144538301143272414025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544770870939430786208133 477144538301143272414025)
                    ·
                      rfl

theorem cell23_2787707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 4].length) (baseStart_2787707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787707 prefixEnd_2787707 := by exact prefixLift 2787707
  have htrace : WordTrace (prefixWord ++ tailWord_2787707) baseStart_2787707 baseEnd_2787707 := by
    simpa [prefixWord, tailWord_2787707, baseEnd_2787707] using wordTrace_append hprefix tailTrace_2787707
  have hstable : (prefixWord ++ tailWord_2787707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787707).length < 2 ^ (prefixWord ++ tailWord_2787707).sum := by decide
  have hdescent : baseEnd_2787707 < baseStart_2787707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787741 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2787741 : Nat := 118140960795 + 2787741 * 2 ^ 59
def prefixEnd_2787741 : Nat := 4983230072969 + 3 ^ 40 * 2787741 * 2
def baseEnd_2787741 : Nat := 477150357748560894738973

theorem tailTrace_2787741 : CollatzResearch.WordTrace tailWord_2787741 prefixEnd_2787741 477150357748560894738973 := by
  unfold tailWord_2787741
  simp only [CollatzResearch.WordTrace]
  refine ⟨101677267393497940102995077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67784844928998626735330051 101677267393497940102995077)
  ·
    refine ⟨19064487636280863769311577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101677267393497940102995077 19064487636280863769311577)
    ·
      refine ⟨14298365727210647826983683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19064487636280863769311577 14298365727210647826983683)
      ·
        refine ⟨21447548590815971740475525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298365727210647826983683 21447548590815971740475525)
        ·
          refine ⟨4021415360777994701339161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21447548590815971740475525 4021415360777994701339161)
          ·
            refine ⟨3016061520583496026004371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021415360777994701339161 3016061520583496026004371)
            ·
              refine ⟨4524092280875244039006557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016061520583496026004371 4524092280875244039006557)
              ·
                refine ⟨1696534605328216514627459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4524092280875244039006557 1696534605328216514627459)
                ·
                  refine ⟨2544801907992324771941189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696534605328216514627459 2544801907992324771941189)
                  ·
                    refine ⟨477150357748560894738973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2544801907992324771941189 477150357748560894738973)
                    ·
                      rfl

theorem cell23_2787741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2787741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787741 prefixEnd_2787741 := by exact prefixLift 2787741
  have htrace : WordTrace (prefixWord ++ tailWord_2787741) baseStart_2787741 baseEnd_2787741 := by
    simpa [prefixWord, tailWord_2787741, baseEnd_2787741] using wordTrace_append hprefix tailTrace_2787741
  have hstable : (prefixWord ++ tailWord_2787741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787741).length < 2 ^ (prefixWord ++ tailWord_2787741).sum := by decide
  have hdescent : baseEnd_2787741 < baseStart_2787741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787787 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 5, 2, 2]
def baseStart_2787787 : Nat := 118140960795 + 2787787 * 2 ^ 59
def prefixEnd_2787787 : Nat := 4983230072969 + 3 ^ 40 * 2787787 * 2
def baseEnd_2787787 : Nat := 1431474693355789504241707

theorem tailTrace_2787787 : CollatzResearch.WordTrace tailWord_2787787 prefixEnd_2787787 1431474693355789504241707 := by
  unfold tailWord_2787787
  simp only [CollatzResearch.WordTrace]
  refine ⟨101678945151331289959169615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67785963434220859972779743 101678945151331289959169615)
  ·
    refine ⟨152518417726996934938754423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101678945151331289959169615 152518417726996934938754423)
    ·
      refine ⟨228777626590495402408131635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152518417726996934938754423 228777626590495402408131635)
      ·
        refine ⟨343166439885743103612197453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228777626590495402408131635 343166439885743103612197453)
        ·
          refine ⟨128687414957153663854574045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343166439885743103612197453 128687414957153663854574045)
          ·
            refine ⟨48257780608932623945465267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128687414957153663854574045 48257780608932623945465267)
            ·
              refine ⟨72386670913398935918197901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48257780608932623945465267 72386670913398935918197901)
              ·
                refine ⟨27145001592524600969324213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72386670913398935918197901 27145001592524600969324213)
                ·
                  refine ⟨2544843899299181340874145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27145001592524600969324213 2544843899299181340874145)
                  ·
                    refine ⟨1908632924474386005655609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544843899299181340874145 1908632924474386005655609)
                    ·
                      refine ⟨1431474693355789504241707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908632924474386005655609 1431474693355789504241707)
                      ·
                        rfl

theorem cell23_2787787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2, 2].length) (baseStart_2787787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787787 prefixEnd_2787787 := by exact prefixLift 2787787
  have htrace : WordTrace (prefixWord ++ tailWord_2787787) baseStart_2787787 baseEnd_2787787 := by
    simpa [prefixWord, tailWord_2787787, baseEnd_2787787] using wordTrace_append hprefix tailTrace_2787787
  have hstable : (prefixWord ++ tailWord_2787787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787787).length < 2 ^ (prefixWord ++ tailWord_2787787).sum := by decide
  have hdescent : baseEnd_2787787 < baseStart_2787787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787807 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_2787807 : Nat := 118140960795 + 2787807 * 2 ^ 59
def prefixEnd_2787807 : Nat := 4983230072969 + 3 ^ 40 * 2787807 * 2
def baseEnd_2787807 : Nat := 1431484962968879425991615

theorem tailTrace_2787807 : CollatzResearch.WordTrace tailWord_2787807 prefixEnd_2787807 1431484962968879425991615 := by
  unfold tailWord_2787807
  simp only [CollatzResearch.WordTrace]
  refine ⟨101679674611258833374897675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67786449740839222249931783 101679674611258833374897675)
  ·
    refine ⟨152519511916888250062346513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101679674611258833374897675 152519511916888250062346513)
    ·
      refine ⟨114389633937666187546759885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152519511916888250062346513 114389633937666187546759885)
      ·
        refine ⟨42896112726624820330034957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114389633937666187546759885 42896112726624820330034957)
        ·
          refine ⟨16086042272484307623763109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42896112726624820330034957 16086042272484307623763109)
          ·
            refine ⟨3016132926090807679455583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16086042272484307623763109 3016132926090807679455583)
            ·
              refine ⟨4524199389136211519183375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016132926090807679455583 4524199389136211519183375)
              ·
                refine ⟨6786299083704317278775063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524199389136211519183375 6786299083704317278775063)
                ·
                  refine ⟨10179448625556475918162595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786299083704317278775063 10179448625556475918162595)
                  ·
                    refine ⟨15269172938334713877243893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10179448625556475918162595 15269172938334713877243893)
                    ·
                      refine ⟨1431484962968879425991615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15269172938334713877243893 1431484962968879425991615)
                      ·
                        rfl

theorem cell23_2787807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_2787807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787807 prefixEnd_2787807 := by exact prefixLift 2787807
  have htrace : WordTrace (prefixWord ++ tailWord_2787807) baseStart_2787807 baseEnd_2787807 := by
    simpa [prefixWord, tailWord_2787807, baseEnd_2787807] using wordTrace_append hprefix tailTrace_2787807
  have hstable : (prefixWord ++ tailWord_2787807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787807).length < 2 ^ (prefixWord ++ tailWord_2787807).sum := by decide
  have hdescent : baseEnd_2787807 < baseStart_2787807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787820 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_2787820 : Nat := 118140960795 + 2787820 * 2 ^ 59
def prefixEnd_2787820 : Nat := 4983230072969 + 3 ^ 40 * 2787820 * 2
def baseEnd_2787820 : Nat := 1431491638217387875129055

theorem tailTrace_2787820 : CollatzResearch.WordTrace tailWord_2787820 prefixEnd_2787820 1431491638217387875129055 := by
  unfold tailWord_2787820
  simp only [CollatzResearch.WordTrace]
  refine ⟨50840074380105868297560457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67786765840141157730080609 50840074380105868297560457)
  ·
    refine ⟨38130055785079401223170343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50840074380105868297560457 38130055785079401223170343)
    ·
      refine ⟨57195083677619101834755515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38130055785079401223170343 57195083677619101834755515)
      ·
        refine ⟨85792625516428652752133273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57195083677619101834755515 85792625516428652752133273)
        ·
          refine ⟨64344469137321489564099955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85792625516428652752133273 64344469137321489564099955)
          ·
            refine ⟨96516703705982234346149933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64344469137321489564099955 96516703705982234346149933)
            ·
              refine ⟨36193763889743337879806225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96516703705982234346149933 36193763889743337879806225)
              ·
                refine ⟨27145322917307503409854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36193763889743337879806225 27145322917307503409854669)
                ·
                  refine ⟨10179496093990313778695501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27145322917307503409854669 10179496093990313778695501)
                  ·
                    refine ⟨3817311035246367667010813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10179496093990313778695501 3817311035246367667010813)
                    ·
                      refine ⟨1431491638217387875129055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817311035246367667010813 1431491638217387875129055)
                      ·
                        rfl

theorem cell23_2787820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_2787820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787820 prefixEnd_2787820 := by exact prefixLift 2787820
  have htrace : WordTrace (prefixWord ++ tailWord_2787820) baseStart_2787820 baseEnd_2787820 := by
    simpa [prefixWord, tailWord_2787820, baseEnd_2787820] using wordTrace_append hprefix tailTrace_2787820
  have hstable : (prefixWord ++ tailWord_2787820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787820).length < 2 ^ (prefixWord ++ tailWord_2787820).sum := by decide
  have hdescent : baseEnd_2787820 < baseStart_2787820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787837 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_2787837 : Nat := 118140960795 + 2787837 * 2 ^ 59
def prefixEnd_2787837 : Nat := 4983230072969 + 3 ^ 40 * 2787837 * 2
def baseEnd_2787837 : Nat := 1431500367388514308616477

theorem tailTrace_2787837 : CollatzResearch.WordTrace tailWord_2787837 prefixEnd_2787837 1431500367388514308616477 := by
  unfold tailWord_2787837
  simp only [CollatzResearch.WordTrace]
  refine ⟨101680768801150148498489765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67787179200766765665659843 101680768801150148498489765)
  ·
    refine ⟨19065144150215652843466831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101680768801150148498489765 19065144150215652843466831)
    ·
      refine ⟨28597716225323479265200247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065144150215652843466831 28597716225323479265200247)
      ·
        refine ⟨42896574337985218897800371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28597716225323479265200247 42896574337985218897800371)
        ·
          refine ⟨64344861506977828346700557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42896574337985218897800371 64344861506977828346700557)
          ·
            refine ⟨24129323065116685630012709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64344861506977828346700557 24129323065116685630012709)
            ·
              refine ⟨4524248074709378555627383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24129323065116685630012709 4524248074709378555627383)
              ·
                refine ⟨6786372112064067833441075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524248074709378555627383 6786372112064067833441075)
                ·
                  refine ⟨10179558168096101750161613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786372112064067833441075 10179558168096101750161613)
                  ·
                    refine ⟨3817334313036038156310605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10179558168096101750161613 3817334313036038156310605)
                    ·
                      refine ⟨1431500367388514308616477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817334313036038156310605 1431500367388514308616477)
                      ·
                        rfl

theorem cell23_2787837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_2787837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787837 prefixEnd_2787837 := by exact prefixLift 2787837
  have htrace : WordTrace (prefixWord ++ tailWord_2787837) baseStart_2787837 baseEnd_2787837 := by
    simpa [prefixWord, tailWord_2787837, baseEnd_2787837] using wordTrace_append hprefix tailTrace_2787837
  have hstable : (prefixWord ++ tailWord_2787837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787837).length < 2 ^ (prefixWord ++ tailWord_2787837).sum := by decide
  have hdescent : baseEnd_2787837 < baseStart_2787837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787850 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2787850 : Nat := 118140960795 + 2787850 * 2 ^ 59
def prefixEnd_2787850 : Nat := 4983230072969 + 3 ^ 40 * 2787850 * 2
def baseEnd_2787850 : Nat := 1431507042637022757753917

theorem tailTrace_2787850 : CollatzResearch.WordTrace tailWord_2787850 prefixEnd_2787850 1431507042637022757753917 := by
  unfold tailWord_2787850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25420310737525762929678251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67787495300068701145808669 25420310737525762929678251)
  ·
    refine ⟨38130466106288644394517377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25420310737525762929678251 38130466106288644394517377)
    ·
      refine ⟨28597849579716483295888033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38130466106288644394517377 28597849579716483295888033)
      ·
        refine ⟨21448387184787362471916025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28597849579716483295888033 21448387184787362471916025)
        ·
          refine ⟨16086290388590521853937019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21448387184787362471916025 16086290388590521853937019)
          ·
            refine ⟨24129435582885782780905529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16086290388590521853937019 24129435582885782780905529)
            ·
              refine ⟨18097076687164337085679147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24129435582885782780905529 18097076687164337085679147)
              ·
                refine ⟨27145615030746505628518721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18097076687164337085679147 27145615030746505628518721)
                ·
                  refine ⟨20359211273059879221389041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27145615030746505628518721 20359211273059879221389041)
                  ·
                    refine ⟨15269408454794909416041781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20359211273059879221389041 15269408454794909416041781)
                    ·
                      refine ⟨1431507042637022757753917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15269408454794909416041781 1431507042637022757753917)
                      ·
                        rfl

theorem cell23_2787850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2787850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787850 prefixEnd_2787850 := by exact prefixLift 2787850
  have htrace : WordTrace (prefixWord ++ tailWord_2787850) baseStart_2787850 baseEnd_2787850 := by
    simpa [prefixWord, tailWord_2787850, baseEnd_2787850] using wordTrace_append hprefix tailTrace_2787850
  have hstable : (prefixWord ++ tailWord_2787850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787850).length < 2 ^ (prefixWord ++ tailWord_2787850).sum := by decide
  have hdescent : baseEnd_2787850 < baseStart_2787850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787877 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_2787877 : Nat := 118140960795 + 2787877 * 2 ^ 59
def prefixEnd_2787877 : Nat := 4983230072969 + 3 ^ 40 * 2787877 * 2
def baseEnd_2787877 : Nat := 1431520906614694152116293

theorem tailTrace_2787877 : CollatzResearch.WordTrace tailWord_2787877 prefixEnd_2787877 1431520906614694152116293 := by
  unfold tailWord_2787877
  simp only [CollatzResearch.WordTrace]
  refine ⟨101682227721005235329945885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67788151814003490219963923 101682227721005235329945885)
  ·
    refine ⟨38130835395376963248729707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101682227721005235329945885 38130835395376963248729707)
    ·
      refine ⟨57196253093065444873094561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38130835395376963248729707 57196253093065444873094561)
      ·
        refine ⟨42897189819799083654820921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57196253093065444873094561 42897189819799083654820921)
        ·
          refine ⟨32172892364849312741115691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42897189819799083654820921 32172892364849312741115691)
          ·
            refine ⟨48259338547273969111673537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32172892364849312741115691 48259338547273969111673537)
            ·
              refine ⟨36194503910455476833755153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48259338547273969111673537 36194503910455476833755153)
              ·
                refine ⟨27145877932841607625316365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36194503910455476833755153 27145877932841607625316365)
                ·
                  refine ⟨10179704224815602859493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27145877932841607625316365 10179704224815602859493637)
                  ·
                    refine ⟨1908694542152925536155057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10179704224815602859493637 1908694542152925536155057)
                    ·
                      refine ⟨1431520906614694152116293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908694542152925536155057 1431520906614694152116293)
                      ·
                        rfl

theorem cell23_2787877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_2787877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787877 prefixEnd_2787877 := by exact prefixLift 2787877
  have htrace : WordTrace (prefixWord ++ tailWord_2787877) baseStart_2787877 baseEnd_2787877 := by
    simpa [prefixWord, tailWord_2787877, baseEnd_2787877] using wordTrace_append hprefix tailTrace_2787877
  have hstable : (prefixWord ++ tailWord_2787877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787877).length < 2 ^ (prefixWord ++ tailWord_2787877).sum := by decide
  have hdescent : baseEnd_2787877 < baseStart_2787877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787885 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2787885 : Nat := 118140960795 + 2787885 * 2 ^ 59
def prefixEnd_2787885 : Nat := 4983230072969 + 3 ^ 40 * 2787885 * 2
def baseEnd_2787885 : Nat := 1431525014459930120816257

theorem tailTrace_2787885 : CollatzResearch.WordTrace tailWord_2787885 prefixEnd_2787885 1431525014459930120816257 := by
  unfold tailWord_2787885
  simp only [CollatzResearch.WordTrace]
  refine ⟨101682519504976252696237109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67788346336650835130824739 101682519504976252696237109)
  ·
    refine ⟨9532736203591523690272229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101682519504976252696237109 9532736203591523690272229)
    ·
      refine ⟨1787388038173410691926043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9532736203591523690272229 1787388038173410691926043)
      ·
        refine ⟨2681082057260116037889065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787388038173410691926043 2681082057260116037889065)
        ·
          refine ⟨2010811542945087028416799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2681082057260116037889065 2010811542945087028416799)
          ·
            refine ⟨3016217314417630542625199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010811542945087028416799 3016217314417630542625199)
            ·
              refine ⟨4524325971626445813937799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016217314417630542625199 4524325971626445813937799)
              ·
                refine ⟨6786488957439668720906699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524325971626445813937799 6786488957439668720906699)
                ·
                  refine ⟨10179733436159503081360049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786488957439668720906699 10179733436159503081360049)
                  ·
                    refine ⟨7634800077119627311020037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10179733436159503081360049 7634800077119627311020037)
                    ·
                      refine ⟨1431525014459930120816257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7634800077119627311020037 1431525014459930120816257)
                      ·
                        rfl

theorem cell23_2787885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2787885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787885 prefixEnd_2787885 := by exact prefixLift 2787885
  have htrace : WordTrace (prefixWord ++ tailWord_2787885) baseStart_2787885 baseEnd_2787885 := by
    simpa [prefixWord, tailWord_2787885, baseEnd_2787885] using wordTrace_append hprefix tailTrace_2787885
  have hstable : (prefixWord ++ tailWord_2787885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787885).length < 2 ^ (prefixWord ++ tailWord_2787885).sum := by decide
  have hdescent : baseEnd_2787885 < baseStart_2787885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2787967 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 6, 2]
def baseStart_2787967 : Nat := 118140960795 + 2787967 * 2 ^ 59
def prefixEnd_2787967 : Nat := 4983230072969 + 3 ^ 40 * 2787967 * 2
def baseEnd_2787967 : Nat := 1431567119873598799990879

theorem tailTrace_2787967 : CollatzResearch.WordTrace tailWord_2787967 prefixEnd_2787967 1431567119873598799990879 := by
  unfold tailWord_2787967
  simp only [CollatzResearch.WordTrace]
  refine ⟨101685510290679180700722155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67790340193786120467148103 101685510290679180700722155)
  ·
    refine ⟨152528265436018771051083233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101685510290679180700722155 152528265436018771051083233)
    ·
      refine ⟨114396199077014078288312425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152528265436018771051083233 114396199077014078288312425)
      ·
        refine ⟨85797149307760558716234319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114396199077014078288312425 85797149307760558716234319)
        ·
          refine ⟨128695723961640838074351479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85797149307760558716234319 128695723961640838074351479)
          ·
            refine ⟨193043585942461257111527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128695723961640838074351479 193043585942461257111527219)
            ·
              refine ⟨289565378913691885667290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193043585942461257111527219 289565378913691885667290829)
              ·
                refine ⟨108587017092634457125234061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289565378913691885667290829 108587017092634457125234061)
                ·
                  refine ⟨40720131409737921421962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108587017092634457125234061 40720131409737921421962773)
                  ·
                    refine ⟨1908756159831465066654505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40720131409737921421962773 1908756159831465066654505)
                    ·
                      refine ⟨1431567119873598799990879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908756159831465066654505 1431567119873598799990879)
                      ·
                        rfl

theorem cell23_2787967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_2787967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2787967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2787967 prefixEnd_2787967 := by exact prefixLift 2787967
  have htrace : WordTrace (prefixWord ++ tailWord_2787967) baseStart_2787967 baseEnd_2787967 := by
    simpa [prefixWord, tailWord_2787967, baseEnd_2787967] using wordTrace_append hprefix tailTrace_2787967
  have hstable : (prefixWord ++ tailWord_2787967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2787967).length < 2 ^ (prefixWord ++ tailWord_2787967).sum := by decide
  have hdescent : baseEnd_2787967 < baseStart_2787967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2787967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788001 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2788001 : Nat := 118140960795 + 2788001 * 2 ^ 59
def prefixEnd_2788001 : Nat := 4983230072969 + 3 ^ 40 * 2788001 * 2
def baseEnd_2788001 : Nat := 1431584578215851666965723

theorem tailTrace_2788001 : CollatzResearch.WordTrace tailWord_2788001 prefixEnd_2788001 1431584578215851666965723 := by
  unfold tailWord_2788001
  simp only [CollatzResearch.WordTrace]
  refine ⟨101686750372556004507459857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67791166915037336338306571 101686750372556004507459857)
  ·
    refine ⟨76265062779417003380594893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101686750372556004507459857 76265062779417003380594893)
    ·
      refine ⟨28599398542281376267723085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76265062779417003380594893 28599398542281376267723085)
      ·
        refine ⟨10724774453355516100396157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28599398542281376267723085 10724774453355516100396157)
        ·
          refine ⟨4021790420008318537648559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10724774453355516100396157 4021790420008318537648559)
          ·
            refine ⟨6032685630012477806472839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021790420008318537648559 6032685630012477806472839)
            ·
              refine ⟨9049028445018716709709259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032685630012477806472839 9049028445018716709709259)
              ·
                refine ⟨13573542667528075064563889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049028445018716709709259 13573542667528075064563889)
                ·
                  refine ⟨10180157000646056298422917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13573542667528075064563889 10180157000646056298422917)
                  ·
                    refine ⟨1908779437621135555954297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10180157000646056298422917 1908779437621135555954297)
                    ·
                      refine ⟨1431584578215851666965723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908779437621135555954297 1431584578215851666965723)
                      ·
                        rfl

theorem cell23_2788001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2788001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788001 prefixEnd_2788001 := by exact prefixLift 2788001
  have htrace : WordTrace (prefixWord ++ tailWord_2788001) baseStart_2788001 baseEnd_2788001 := by
    simpa [prefixWord, tailWord_2788001, baseEnd_2788001] using wordTrace_append hprefix tailTrace_2788001
  have hstable : (prefixWord ++ tailWord_2788001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788001).length < 2 ^ (prefixWord ++ tailWord_2788001).sum := by decide
  have hdescent : baseEnd_2788001 < baseStart_2788001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788021 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2788021 : Nat := 118140960795 + 2788021 * 2 ^ 59
def prefixEnd_2788021 : Nat := 4983230072969 + 3 ^ 40 * 2788021 * 2
def baseEnd_2788021 : Nat := 1431594847828941588715631

theorem tailTrace_2788021 : CollatzResearch.WordTrace tailWord_2788021 prefixEnd_2788021 1431594847828941588715631 := by
  unfold tailWord_2788021
  simp only [CollatzResearch.WordTrace]
  refine ⟨101687479832483547923187917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67791653221655698615458611 101687479832483547923187917)
  ·
    refine ⟨38132804937181330471195469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101687479832483547923187917 38132804937181330471195469)
    ·
      refine ⟨14299801851442998926698301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38132804937181330471195469 14299801851442998926698301)
      ·
        refine ⟨5362425694291124597511863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14299801851442998926698301 5362425694291124597511863)
        ·
          refine ⟨8043638541436686896267795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362425694291124597511863 8043638541436686896267795)
          ·
            refine ⟨12065457812155030344401693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043638541436686896267795 12065457812155030344401693)
            ·
              refine ⟨4524546679558136379150635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12065457812155030344401693 4524546679558136379150635)
              ·
                refine ⟨6786820019337204568725953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524546679558136379150635 6786820019337204568725953)
                ·
                  refine ⟨5090115014502903426544465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6786820019337204568725953 5090115014502903426544465)
                  ·
                    refine ⟨3817586260877177569908349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090115014502903426544465 3817586260877177569908349)
                    ·
                      refine ⟨1431594847828941588715631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817586260877177569908349 1431594847828941588715631)
                      ·
                        rfl

theorem cell23_2788021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2788021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788021 prefixEnd_2788021 := by exact prefixLift 2788021
  have htrace : WordTrace (prefixWord ++ tailWord_2788021) baseStart_2788021 baseEnd_2788021 := by
    simpa [prefixWord, tailWord_2788021, baseEnd_2788021] using wordTrace_append hprefix tailTrace_2788021
  have hstable : (prefixWord ++ tailWord_2788021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788021).length < 2 ^ (prefixWord ++ tailWord_2788021).sum := by decide
  have hdescent : baseEnd_2788021 < baseStart_2788021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788074 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_2788074 : Nat := 118140960795 + 2788074 * 2 ^ 59
def prefixEnd_2788074 : Nat := 4983230072969 + 3 ^ 40 * 2788074 * 2
def baseEnd_2788074 : Nat := 1431622062303629881352887

theorem tailTrace_2788074 : CollatzResearch.WordTrace tailWord_2788074 prefixEnd_2788074 1431622062303629881352887 := by
  unfold tailWord_2788074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422353225322884493716819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67792941934194358649911517 25422353225322884493716819)
  ·
    refine ⟨38133529837984326740575229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25422353225322884493716819 38133529837984326740575229)
    ·
      refine ⟨14300073689244122527715711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38133529837984326740575229 14300073689244122527715711)
      ·
        refine ⟨21450110533866183791573567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14300073689244122527715711 21450110533866183791573567)
        ·
          refine ⟨32175165800799275687360351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21450110533866183791573567 32175165800799275687360351)
          ·
            refine ⟨48262748701198913531040527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32175165800799275687360351 48262748701198913531040527)
            ·
              refine ⟨72394123051798370296560791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48262748701198913531040527 72394123051798370296560791)
              ·
                refine ⟨108591184577697555444841187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72394123051798370296560791 108591184577697555444841187)
                ·
                  refine ⟨162886776866546333167261781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108591184577697555444841187 162886776866546333167261781)
                  ·
                    refine ⟨1908829416404839841803849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 162886776866546333167261781 1908829416404839841803849)
                    ·
                      refine ⟨1431622062303629881352887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908829416404839841803849 1431622062303629881352887)
                      ·
                        rfl

theorem cell23_2788074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_2788074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788074 prefixEnd_2788074 := by exact prefixLift 2788074
  have htrace : WordTrace (prefixWord ++ tailWord_2788074) baseStart_2788074 baseEnd_2788074 := by
    simpa [prefixWord, tailWord_2788074, baseEnd_2788074] using wordTrace_append hprefix tailTrace_2788074
  have hstable : (prefixWord ++ tailWord_2788074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788074).length < 2 ^ (prefixWord ++ tailWord_2788074).sum := by decide
  have hdescent : baseEnd_2788074 < baseStart_2788074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788087 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2788087 : Nat := 118140960795 + 2788087 * 2 ^ 59
def prefixEnd_2788087 : Nat := 4983230072969 + 3 ^ 40 * 2788087 * 2
def baseEnd_2788087 : Nat := 1431628737552138330490327

theorem tailTrace_2788087 : CollatzResearch.WordTrace tailWord_2788087 prefixEnd_2788087 1431628737552138330490327 := by
  unfold tailWord_2788087
  simp only [CollatzResearch.WordTrace]
  refine ⟨101689887050244441195090515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67793258033496294130060343 101689887050244441195090515)
  ·
    refine ⟨152534830575366661792635773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101689887050244441195090515 152534830575366661792635773)
    ·
      refine ⟨57200561465762498172238415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152534830575366661792635773 57200561465762498172238415)
      ·
        refine ⟨85800842198643747258357623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57200561465762498172238415 85800842198643747258357623)
        ·
          refine ⟨128701263297965620887536435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85800842198643747258357623 128701263297965620887536435)
          ·
            refine ⟨193051894946948431331304653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128701263297965620887536435 193051894946948431331304653)
            ·
              refine ⟨72394460605105661749239245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193051894946948431331304653 72394460605105661749239245)
              ·
                refine ⟨27147922726914623155964717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72394460605105661749239245 27147922726914623155964717)
                ·
                  refine ⟨10180471022592983683486769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27147922726914623155964717 10180471022592983683486769)
                  ·
                    refine ⟨7635353266944737762615077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10180471022592983683486769 7635353266944737762615077)
                    ·
                      refine ⟨1431628737552138330490327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7635353266944737762615077 1431628737552138330490327)
                      ·
                        rfl

theorem cell23_2788087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2788087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788087 prefixEnd_2788087 := by exact prefixLift 2788087
  have htrace : WordTrace (prefixWord ++ tailWord_2788087) baseStart_2788087 baseEnd_2788087 := by
    simpa [prefixWord, tailWord_2788087, baseEnd_2788087] using wordTrace_append hprefix tailTrace_2788087
  have hstable : (prefixWord ++ tailWord_2788087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788087).length < 2 ^ (prefixWord ++ tailWord_2788087).sum := by decide
  have hdescent : baseEnd_2788087 < baseStart_2788087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788117 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2788117 : Nat := 118140960795 + 2788117 * 2 ^ 59
def prefixEnd_2788117 : Nat := 4983230072969 + 3 ^ 40 * 2788117 * 2
def baseEnd_2788117 : Nat := 1431644141971773213115189

theorem tailTrace_2788117 : CollatzResearch.WordTrace tailWord_2788117 prefixEnd_2788117 1431644141971773213115189 := by
  unfold tailWord_2788117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101690981240135756318682605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67793987493423837545788403 101690981240135756318682605)
  ·
    refine ⟨38134117965050908619505977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101690981240135756318682605 38134117965050908619505977)
    ·
      refine ⟨28600588473788181464629483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38134117965050908619505977 28600588473788181464629483)
      ·
        refine ⟨42900882710682272196944225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28600588473788181464629483 42900882710682272196944225)
        ·
          refine ⟨32175662033011704147708169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42900882710682272196944225 32175662033011704147708169)
          ·
            refine ⟨24131746524758778110781127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32175662033011704147708169 24131746524758778110781127)
            ·
              refine ⟨36197619787138167166171691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24131746524758778110781127 36197619787138167166171691)
              ·
                refine ⟨54296429680707250749257537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36197619787138167166171691 54296429680707250749257537)
                ·
                  refine ⟨40722322260530438061943153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54296429680707250749257537 40722322260530438061943153)
                  ·
                    refine ⟨30541741695397828546457365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40722322260530438061943153 30541741695397828546457365)
                    ·
                      refine ⟨1431644141971773213115189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30541741695397828546457365 1431644141971773213115189)
                      ·
                        rfl

theorem cell23_2788117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2788117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788117 prefixEnd_2788117 := by exact prefixLift 2788117
  have htrace : WordTrace (prefixWord ++ tailWord_2788117) baseStart_2788117 baseEnd_2788117 := by
    simpa [prefixWord, tailWord_2788117, baseEnd_2788117] using wordTrace_append hprefix tailTrace_2788117
  have hstable : (prefixWord ++ tailWord_2788117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788117).length < 2 ^ (prefixWord ++ tailWord_2788117).sum := by decide
  have hdescent : baseEnd_2788117 < baseStart_2788117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788125 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2788125 : Nat := 118140960795 + 2788125 * 2 ^ 59
def prefixEnd_2788125 : Nat := 4983230072969 + 3 ^ 40 * 2788125 * 2
def baseEnd_2788125 : Nat := 1431648249817009181815153

theorem tailTrace_2788125 : CollatzResearch.WordTrace tailWord_2788125 prefixEnd_2788125 1431648249817009181815153 := by
  unfold tailWord_2788125
  simp only [CollatzResearch.WordTrace]
  refine ⟨101691273024106773684973829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67794182016071182456649219 101691273024106773684973829)
  ·
    refine ⟨19067113692020020065932593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101691273024106773684973829 19067113692020020065932593)
    ·
      refine ⟨14300335269015015049449445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19067113692020020065932593 14300335269015015049449445)
      ·
        refine ⟨2681312862940315321771771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14300335269015015049449445 2681312862940315321771771)
        ·
          refine ⟨4021969294410472982657657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681312862940315321771771 4021969294410472982657657)
          ·
            refine ⟨3016476970807854736993243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021969294410472982657657 3016476970807854736993243)
            ·
              refine ⟨4524715456211782105489865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016476970807854736993243 4524715456211782105489865)
              ·
                refine ⟨3393536592158836579117399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524715456211782105489865 3393536592158836579117399)
                ·
                  refine ⟨5090304888238254868676099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393536592158836579117399 5090304888238254868676099)
                  ·
                    refine ⟨7635457332357382303014149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090304888238254868676099 7635457332357382303014149)
                    ·
                      refine ⟨1431648249817009181815153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7635457332357382303014149 1431648249817009181815153)
                      ·
                        rfl

theorem cell23_2788125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2788125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788125 prefixEnd_2788125 := by exact prefixLift 2788125
  have htrace : WordTrace (prefixWord ++ tailWord_2788125) baseStart_2788125 baseEnd_2788125 := by
    simpa [prefixWord, tailWord_2788125, baseEnd_2788125] using wordTrace_append hprefix tailTrace_2788125
  have hstable : (prefixWord ++ tailWord_2788125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788125).length < 2 ^ (prefixWord ++ tailWord_2788125).sum := by decide
  have hdescent : baseEnd_2788125 < baseStart_2788125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788128 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2788128 : Nat := 118140960795 + 2788128 * 2 ^ 59
def prefixEnd_2788128 : Nat := 4983230072969 + 3 ^ 40 * 2788128 * 2
def baseEnd_2788128 : Nat := 1431649790258972670077639

theorem tailTrace_2788128 : CollatzResearch.WordTrace tailWord_2788128 prefixEnd_2788128 1431649790258972670077639 := by
  unfold tailWord_2788128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50845691221547952598666519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67794254962063936798222025 50845691221547952598666519)
  ·
    refine ⟨76268536832321928897999779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50845691221547952598666519 76268536832321928897999779)
    ·
      refine ⟨114402805248482893346999669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76268536832321928897999779 114402805248482893346999669)
      ·
        refine ⟨10725262992045271251281219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114402805248482893346999669 10725262992045271251281219)
        ·
          refine ⟨16087894488067906876921829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725262992045271251281219 16087894488067906876921829)
          ·
            refine ⟨3016480216512732539422843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16087894488067906876921829 3016480216512732539422843)
            ·
              refine ⟨4524720324769098809134265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016480216512732539422843 4524720324769098809134265)
              ·
                refine ⟨3393540243576824106850699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524720324769098809134265 3393540243576824106850699)
                ·
                  refine ⟨5090310365365236160276049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393540243576824106850699 5090310365365236160276049)
                  ·
                    refine ⟨3817732774023927120207037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090310365365236160276049 3817732774023927120207037)
                    ·
                      refine ⟨1431649790258972670077639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817732774023927120207037 1431649790258972670077639)
                      ·
                        rfl

theorem cell23_2788128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2788128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788128 prefixEnd_2788128 := by exact prefixLift 2788128
  have htrace : WordTrace (prefixWord ++ tailWord_2788128) baseStart_2788128 baseEnd_2788128 := by
    simpa [prefixWord, tailWord_2788128, baseEnd_2788128] using wordTrace_append hprefix tailTrace_2788128
  have hstable : (prefixWord ++ tailWord_2788128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788128).length < 2 ^ (prefixWord ++ tailWord_2788128).sum := by decide
  have hdescent : baseEnd_2788128 < baseStart_2788128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788138 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2788138 : Nat := 118140960795 + 2788138 * 2 ^ 59
def prefixEnd_2788138 : Nat := 4983230072969 + 3 ^ 40 * 2788138 * 2
def baseEnd_2788138 : Nat := 1431654925065517630952593

theorem tailTrace_2788138 : CollatzResearch.WordTrace tailWord_2788138 prefixEnd_2788138 1431654925065517630952593 := by
  unfold tailWord_2788138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422936793264919226299267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67794498115373117936798045 25422936793264919226299267)
  ·
    refine ⟨38134405189897378839448901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25422936793264919226299267 38134405189897378839448901)
    ·
      refine ⟨7150200973105758532396669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38134405189897378839448901 7150200973105758532396669)
      ·
        refine ⟨2681325364914659449648751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7150200973105758532396669 2681325364914659449648751)
        ·
          refine ⟨4021988047371989174473127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681325364914659449648751 4021988047371989174473127)
          ·
            refine ⟨6032982071057983761709691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021988047371989174473127 6032982071057983761709691)
            ·
              refine ⟨9049473106586975642564537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032982071057983761709691 9049473106586975642564537)
              ·
                refine ⟨6787104829940231731923403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9049473106586975642564537 6787104829940231731923403)
                ·
                  refine ⟨10180657244910347597885105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787104829940231731923403 10180657244910347597885105)
                  ·
                    refine ⟨7635492933682760698413829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10180657244910347597885105 7635492933682760698413829)
                    ·
                      refine ⟨1431654925065517630952593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7635492933682760698413829 1431654925065517630952593)
                      ·
                        rfl

theorem cell23_2788138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2788138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788138 prefixEnd_2788138 := by exact prefixLift 2788138
  have htrace : WordTrace (prefixWord ++ tailWord_2788138) baseStart_2788138 baseEnd_2788138 := by
    simpa [prefixWord, tailWord_2788138, baseEnd_2788138] using wordTrace_append hprefix tailTrace_2788138
  have hstable : (prefixWord ++ tailWord_2788138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788138).length < 2 ^ (prefixWord ++ tailWord_2788138).sum := by decide
  have hdescent : baseEnd_2788138 < baseStart_2788138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788221 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2788221 : Nat := 118140960795 + 2788221 * 2 ^ 59
def prefixEnd_2788221 : Nat := 4983230072969 + 3 ^ 40 * 2788221 * 2
def baseEnd_2788221 : Nat := 159077504884426756246079

theorem tailTrace_2788221 : CollatzResearch.WordTrace tailWord_2788221 prefixEnd_2788221 159077504884426756246079 := by
  unfold tailWord_2788221
  simp only [CollatzResearch.WordTrace]
  refine ⟨101694774431758982080468517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67796516287839321386979011 101694774431758982080468517)
  ·
    refine ⟨19067770205954809140087847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101694774431758982080468517 19067770205954809140087847)
    ·
      refine ⟨28601655308932213710131771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19067770205954809140087847 28601655308932213710131771)
      ·
        refine ⟨42902482963398320565197657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28601655308932213710131771 42902482963398320565197657)
        ·
          refine ⟨32176862222548740423898243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42902482963398320565197657 32176862222548740423898243)
          ·
            refine ⟨48265293333823110635847365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32176862222548740423898243 48265293333823110635847365)
            ·
              refine ⟨9049742500091833244221381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48265293333823110635847365 9049742500091833244221381)
              ·
                refine ⟨1696826718767218733291509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9049742500091833244221381 1696826718767218733291509)
                ·
                  refine ⟨159077504884426756246079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1696826718767218733291509 159077504884426756246079)
                  ·
                    rfl

theorem cell23_2788221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2788221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788221 prefixEnd_2788221 := by exact prefixLift 2788221
  have htrace : WordTrace (prefixWord ++ tailWord_2788221) baseStart_2788221 baseEnd_2788221 := by
    simpa [prefixWord, tailWord_2788221, baseEnd_2788221] using wordTrace_append hprefix tailTrace_2788221
  have hstable : (prefixWord ++ tailWord_2788221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788221).length < 2 ^ (prefixWord ++ tailWord_2788221).sum := by decide
  have hdescent : baseEnd_2788221 < baseStart_2788221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788231 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2788231 : Nat := 118140960795 + 2788231 * 2 ^ 59
def prefixEnd_2788231 : Nat := 4983230072969 + 3 ^ 40 * 2788231 * 2
def baseEnd_2788231 : Nat := 1431702678766385767089665

theorem tailTrace_2788231 : CollatzResearch.WordTrace tailWord_2788231 prefixEnd_2788231 1431702678766385767089665 := by
  unfold tailWord_2788231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101695139161722753788332547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67796759441148502525555031 101695139161722753788332547)
  ·
    refine ⟨152542708742584130682498821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101695139161722753788332547 152542708742584130682498821)
    ·
      refine ⟨28601757889234524502968529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152542708742584130682498821 28601757889234524502968529)
      ·
        refine ⟨21451318416925893377226397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28601757889234524502968529 21451318416925893377226397)
        ·
          refine ⟨8044244406347210016459899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21451318416925893377226397 8044244406347210016459899)
          ·
            refine ⟨12066366609520815024689849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044244406347210016459899 12066366609520815024689849)
            ·
              refine ⟨9049774957140611268517387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12066366609520815024689849 9049774957140611268517387)
              ·
                refine ⟨13574662435710916902776081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049774957140611268517387 13574662435710916902776081)
                ·
                  refine ⟨10180996826783187677082061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13574662435710916902776081 10180996826783187677082061)
                  ·
                    refine ⟨3817873810043695378905773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10180996826783187677082061 3817873810043695378905773)
                    ·
                      refine ⟨1431702678766385767089665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817873810043695378905773 1431702678766385767089665)
                      ·
                        rfl

theorem cell23_2788231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2788231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788231 prefixEnd_2788231 := by exact prefixLift 2788231
  have htrace : WordTrace (prefixWord ++ tailWord_2788231) baseStart_2788231 baseEnd_2788231 := by
    simpa [prefixWord, tailWord_2788231, baseEnd_2788231] using wordTrace_append hprefix tailTrace_2788231
  have hstable : (prefixWord ++ tailWord_2788231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788231).length < 2 ^ (prefixWord ++ tailWord_2788231).sum := by decide
  have hdescent : baseEnd_2788231 < baseStart_2788231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788232 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2788232 : Nat := 118140960795 + 2788232 * 2 ^ 59
def prefixEnd_2788232 : Nat := 4983230072969 + 3 ^ 40 * 2788232 * 2
def baseEnd_2788232 : Nat := 1431703192247040263177161

theorem tailTrace_2788232 : CollatzResearch.WordTrace tailWord_2788232 prefixEnd_2788232 1431703192247040263177161 := by
  unfold tailWord_2788232
  simp only [CollatzResearch.WordTrace]
  refine ⟨50847587817359565479559475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67796783756479420639412633 50847587817359565479559475)
  ·
    refine ⟨76271381726039348219339213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50847587817359565479559475 76271381726039348219339213)
    ·
      refine ⟨28601768147264755582252205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76271381726039348219339213 28601768147264755582252205)
      ·
        refine ⟨10725663055224283343344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28601768147264755582252205 10725663055224283343344577)
        ·
          refine ⟨8044247291418212507508433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10725663055224283343344577 8044247291418212507508433)
          ·
            refine ⟨6033185468563659380631325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044247291418212507508433 6033185468563659380631325)
            ·
              refine ⟨2262444550711372267736747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033185468563659380631325 2262444550711372267736747)
              ·
                refine ⟨3393666826067058401605121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262444550711372267736747 3393666826067058401605121)
                ·
                  refine ⟨2545250119550293801203841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393666826067058401605121 2545250119550293801203841)
                  ·
                    refine ⟨1908937589662720350902881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545250119550293801203841 1908937589662720350902881)
                    ·
                      refine ⟨1431703192247040263177161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908937589662720350902881 1431703192247040263177161)
                      ·
                        rfl

theorem cell23_2788232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2788232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788232 prefixEnd_2788232 := by exact prefixLift 2788232
  have htrace : WordTrace (prefixWord ++ tailWord_2788232) baseStart_2788232 baseEnd_2788232 := by
    simpa [prefixWord, tailWord_2788232, baseEnd_2788232] using wordTrace_append hprefix tailTrace_2788232
  have hstable : (prefixWord ++ tailWord_2788232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788232).length < 2 ^ (prefixWord ++ tailWord_2788232).sum := by decide
  have hdescent : baseEnd_2788232 < baseStart_2788232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788271 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 4, 2]
def baseStart_2788271 : Nat := 118140960795 + 2788271 * 2 ^ 59
def prefixEnd_2788271 : Nat := 4983230072969 + 3 ^ 40 * 2788271 * 2
def baseEnd_2788271 : Nat := 1431723217992565610589481

theorem tailTrace_2788271 : CollatzResearch.WordTrace tailWord_2788271 prefixEnd_2788271 1431723217992565610589481 := by
  unfold tailWord_2788271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101696598081577840619788667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67797732054385227079859111 101696598081577840619788667)
  ·
    refine ⟨152544897122366760929683001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101696598081577840619788667 152544897122366760929683001)
    ·
      refine ⟨114408672841775070697262251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152544897122366760929683001 114408672841775070697262251)
      ·
        refine ⟨171613009262662606045893377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114408672841775070697262251 171613009262662606045893377)
        ·
          refine ⟨128709756946996954534420033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171613009262662606045893377 128709756946996954534420033)
          ·
            refine ⟨96532317710247715900815025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128709756946996954534420033 96532317710247715900815025)
            ·
              refine ⟨72399238282685786925611269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96532317710247715900815025 72399238282685786925611269)
              ·
                refine ⟨13574857178003585048552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72399238282685786925611269 13574857178003585048552113)
                ·
                  refine ⟨10181142883502688786414085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13574857178003585048552113 10181142883502688786414085)
                  ·
                    refine ⟨1908964290656754147452641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10181142883502688786414085 1908964290656754147452641)
                    ·
                      refine ⟨1431723217992565610589481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1908964290656754147452641 1431723217992565610589481)
                      ·
                        rfl

theorem cell23_2788271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 4, 2].length) (baseStart_2788271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788271 prefixEnd_2788271 := by exact prefixLift 2788271
  have htrace : WordTrace (prefixWord ++ tailWord_2788271) baseStart_2788271 baseEnd_2788271 := by
    simpa [prefixWord, tailWord_2788271, baseEnd_2788271] using wordTrace_append hprefix tailTrace_2788271
  have hstable : (prefixWord ++ tailWord_2788271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788271).length < 2 ^ (prefixWord ++ tailWord_2788271).sum := by decide
  have hdescent : baseEnd_2788271 < baseStart_2788271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788308 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2788308 : Nat := 118140960795 + 2788308 * 2 ^ 59
def prefixEnd_2788308 : Nat := 4983230072969 + 3 ^ 40 * 2788308 * 2
def baseEnd_2788308 : Nat := 1431742216776781965826811

theorem tailTrace_2788308 : CollatzResearch.WordTrace tailWord_2788308 prefixEnd_2788308 1431742216776781965826811 := by
  unfold tailWord_2788308
  simp only [CollatzResearch.WordTrace]
  refine ⟨50848973791221897969442789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67798631721629197292590385 50848973791221897969442789)
  ·
    refine ⟨9534182585854105869270523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50848973791221897969442789 9534182585854105869270523)
    ·
      refine ⟨14301273878781158803905785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534182585854105869270523 14301273878781158803905785)
      ·
        refine ⟨10725955409085869102929339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14301273878781158803905785 10725955409085869102929339)
        ·
          refine ⟨16088933113628803654394009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725955409085869102929339 16088933113628803654394009)
          ·
            refine ⟨12066699835221602740795507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16088933113628803654394009 12066699835221602740795507)
            ·
              refine ⟨18100049752832404111193261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12066699835221602740795507 18100049752832404111193261)
              ·
                refine ⟨6787518657312151541697473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18100049752832404111193261 6787518657312151541697473)
                ·
                  refine ⟨5090638992984113656273105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787518657312151541697473 5090638992984113656273105)
                  ·
                    refine ⟨3817979244738085242204829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090638992984113656273105 3817979244738085242204829)
                    ·
                      refine ⟨1431742216776781965826811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3817979244738085242204829 1431742216776781965826811)
                      ·
                        rfl

theorem cell23_2788308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2788308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788308 prefixEnd_2788308 := by exact prefixLift 2788308
  have htrace : WordTrace (prefixWord ++ tailWord_2788308) baseStart_2788308 baseEnd_2788308 := by
    simpa [prefixWord, tailWord_2788308, baseEnd_2788308] using wordTrace_append hprefix tailTrace_2788308
  have hstable : (prefixWord ++ tailWord_2788308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788308).length < 2 ^ (prefixWord ++ tailWord_2788308).sum := by decide
  have hdescent : baseEnd_2788308 < baseStart_2788308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788331 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 5, 2]
def baseStart_2788331 : Nat := 118140960795 + 2788331 * 2 ^ 59
def prefixEnd_2788331 : Nat := 4983230072969 + 3 ^ 40 * 2788331 * 2
def baseEnd_2788331 : Nat := 1431754026831835375839205

theorem tailTrace_2788331 : CollatzResearch.WordTrace tailWord_2788331 prefixEnd_2788331 1431754026831835375839205 := by
  unfold tailWord_2788331
  simp only [CollatzResearch.WordTrace]
  refine ⟨101698786461360470866972847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67799190974240313911315231 101698786461360470866972847)
  ·
    refine ⟨152548179692040706300459271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101698786461360470866972847 152548179692040706300459271)
    ·
      refine ⟨228822269538061059450688907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152548179692040706300459271 228822269538061059450688907)
      ·
        refine ⟨343233404307091589176033361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228822269538061059450688907 343233404307091589176033361)
        ·
          refine ⟨257425053230318691882025021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343233404307091589176033361 257425053230318691882025021)
          ·
            refine ⟨96534394961369509455759383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257425053230318691882025021 96534394961369509455759383)
            ·
              refine ⟨144801592442054264183639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96534394961369509455759383 144801592442054264183639075)
              ·
                refine ⟨217202388663081396275458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144801592442054264183639075 217202388663081396275458613)
                ·
                  refine ⟨20362723937163880900824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217202388663081396275458613 20362723937163880900824245)
                  ·
                    refine ⟨1909005369109113834452273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20362723937163880900824245 1909005369109113834452273)
                    ·
                      refine ⟨1431754026831835375839205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909005369109113834452273 1431754026831835375839205)
                      ·
                        rfl

theorem cell23_2788331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 5, 2].length) (baseStart_2788331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788331 prefixEnd_2788331 := by exact prefixLift 2788331
  have htrace : WordTrace (prefixWord ++ tailWord_2788331) baseStart_2788331 baseEnd_2788331 := by
    simpa [prefixWord, tailWord_2788331, baseEnd_2788331] using wordTrace_append hprefix tailTrace_2788331
  have hstable : (prefixWord ++ tailWord_2788331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788331).length < 2 ^ (prefixWord ++ tailWord_2788331).sum := by decide
  have hdescent : baseEnd_2788331 < baseStart_2788331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788371 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 4, 4]
def baseStart_2788371 : Nat := 118140960795 + 2788371 * 2 ^ 59
def prefixEnd_2788371 : Nat := 4983230072969 + 3 ^ 40 * 2788371 * 2
def baseEnd_2788371 : Nat := 477258188686005073113007

theorem tailTrace_2788371 : CollatzResearch.WordTrace tailWord_2788371 prefixEnd_2788371 477258188686005073113007 := by
  unfold tailWord_2788371
  simp only [CollatzResearch.WordTrace]
  refine ⟨101700245381215557698428967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67800163587477038465619311 101700245381215557698428967)
  ·
    refine ⟨152550368071823336547643451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101700245381215557698428967 152550368071823336547643451)
    ·
      refine ⟨228825552107735004821465177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152550368071823336547643451 228825552107735004821465177)
      ·
        refine ⟨171619164080801253616098883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228825552107735004821465177 171619164080801253616098883)
        ·
          refine ⟨257428746121201880424148325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171619164080801253616098883 257428746121201880424148325)
          ·
            refine ⟨48267889897725352579527811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257428746121201880424148325 48267889897725352579527811)
            ·
              refine ⟨72401834846588028869291717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48267889897725352579527811 72401834846588028869291717)
              ·
                refine ⟨13575344033735255412992197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72401834846588028869291717 13575344033735255412992197)
                ·
                  refine ⟨2545377006325360389936037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13575344033735255412992197 2545377006325360389936037)
                  ·
                    refine ⟨477258188686005073113007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545377006325360389936037 477258188686005073113007)
                    ·
                      rfl

theorem cell23_2788371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 4].length) (baseStart_2788371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788371 prefixEnd_2788371 := by exact prefixLift 2788371
  have htrace : WordTrace (prefixWord ++ tailWord_2788371) baseStart_2788371 baseEnd_2788371 := by
    simpa [prefixWord, tailWord_2788371, baseEnd_2788371] using wordTrace_append hprefix tailTrace_2788371
  have hstable : (prefixWord ++ tailWord_2788371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788371).length < 2 ^ (prefixWord ++ tailWord_2788371).sum := by decide
  have hdescent : baseEnd_2788371 < baseStart_2788371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788375 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 1, 5]
def baseStart_2788375 : Nat := 118140960795 + 2788375 * 2 ^ 59
def prefixEnd_2788375 : Nat := 4983230072969 + 3 ^ 40 * 2788375 * 2
def baseEnd_2788375 : Nat := 477258873326877734563001

theorem tailTrace_2788375 : CollatzResearch.WordTrace tailWord_2788375 prefixEnd_2788375 477258873326877734563001 := by
  unfold tailWord_2788375
  simp only [CollatzResearch.WordTrace]
  refine ⟨101700391273201066381574579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67800260848800710921049719 101700391273201066381574579)
  ·
    refine ⟨152550586909801599572361869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101700391273201066381574579 152550586909801599572361869)
    ·
      refine ⟨57206470091175599839635701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152550586909801599572361869 57206470091175599839635701)
      ·
        refine ⟨5363106571047712484965847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57206470091175599839635701 5363106571047712484965847)
        ·
          refine ⟨8044659856571568727448771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363106571047712484965847 8044659856571568727448771)
          ·
            refine ⟨12066989784857353091173157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044659856571568727448771 12066989784857353091173157)
            ·
              refine ⟨2262560584660753704594967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12066989784857353091173157 2262560584660753704594967)
              ·
                refine ⟨3393840876991130556892451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262560584660753704594967 3393840876991130556892451)
                ·
                  refine ⟨5090761315486695835338677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393840876991130556892451 5090761315486695835338677)
                  ·
                    refine ⟨477258873326877734563001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5090761315486695835338677 477258873326877734563001)
                    ·
                      rfl

theorem cell23_2788375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_2788375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788375 prefixEnd_2788375 := by exact prefixLift 2788375
  have htrace : WordTrace (prefixWord ++ tailWord_2788375) baseStart_2788375 baseEnd_2788375 := by
    simpa [prefixWord, tailWord_2788375, baseEnd_2788375] using wordTrace_append hprefix tailTrace_2788375
  have hstable : (prefixWord ++ tailWord_2788375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788375).length < 2 ^ (prefixWord ++ tailWord_2788375).sum := by decide
  have hdescent : baseEnd_2788375 < baseStart_2788375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788378 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2788378 : Nat := 118140960795 + 2788378 * 2 ^ 59
def prefixEnd_2788378 : Nat := 4983230072969 + 3 ^ 40 * 2788378 * 2
def baseEnd_2788378 : Nat := 1431778160422596691951489

theorem tailTrace_2788378 : CollatzResearch.WordTrace tailWord_2788378 prefixEnd_2788378 1431778160422596691951489 := by
  unfold tailWord_2788378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25425125173047549473483447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67800333794793465262622525 25425125173047549473483447)
  ·
    refine ⟨38137687759571324210225171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25425125173047549473483447 38137687759571324210225171)
    ·
      refine ⟨57206531639356986315337757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38137687759571324210225171 57206531639356986315337757)
      ·
        refine ⟨21452449364758869868251659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57206531639356986315337757 21452449364758869868251659)
        ·
          refine ⟨32178674047138304802377489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21452449364758869868251659 32178674047138304802377489)
          ·
            refine ⟨24134005535353728601783117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32178674047138304802377489 24134005535353728601783117)
            ·
              refine ⟨9050252075757648225668669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24134005535353728601783117 9050252075757648225668669)
              ·
                refine ⟨3393844528409118084625751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050252075757648225668669 3393844528409118084625751)
                ·
                  refine ⟨5090766792613677126938627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393844528409118084625751 5090766792613677126938627)
                  ·
                    refine ⟨7636150188920515690407941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090766792613677126938627 7636150188920515690407941)
                    ·
                      refine ⟨1431778160422596691951489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7636150188920515690407941 1431778160422596691951489)
                      ·
                        rfl

theorem cell23_2788378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2788378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788378 prefixEnd_2788378 := by exact prefixLift 2788378
  have htrace : WordTrace (prefixWord ++ tailWord_2788378) baseStart_2788378 baseEnd_2788378 := by
    simpa [prefixWord, tailWord_2788378, baseEnd_2788378] using wordTrace_append hprefix tailTrace_2788378
  have hstable : (prefixWord ++ tailWord_2788378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788378).length < 2 ^ (prefixWord ++ tailWord_2788378).sum := by decide
  have hdescent : baseEnd_2788378 < baseStart_2788378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788395 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 3, 2, 2]
def baseStart_2788395 : Nat := 118140960795 + 2788395 * 2 ^ 59
def prefixEnd_2788395 : Nat := 4983230072969 + 3 ^ 40 * 2788395 * 2
def baseEnd_2788395 : Nat := 1431786889593723125438911

theorem tailTrace_2788395 : CollatzResearch.WordTrace tailWord_2788395 prefixEnd_2788395 1431786889593723125438911 := by
  unfold tailWord_2788395
  simp only [CollatzResearch.WordTrace]
  refine ⟨101701120733128609797302639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67800747155419073198201759 101701120733128609797302639)
  ·
    refine ⟨152551681099692914695953959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101701120733128609797302639 152551681099692914695953959)
    ·
      refine ⟨228827521649539372043930939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152551681099692914695953959 228827521649539372043930939)
      ·
        refine ⟨343241282474309058065896409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228827521649539372043930939 343241282474309058065896409)
        ·
          refine ⟨257430961855731793549422307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343241282474309058065896409 257430961855731793549422307)
          ·
            refine ⟨386146442783597690324133461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257430961855731793549422307 386146442783597690324133461)
            ·
              refine ⟨4525153626370285433485939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 386146442783597690324133461 4525153626370285433485939)
              ·
                refine ⟨6787730439555428150228909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525153626370285433485939 6787730439555428150228909)
                ·
                  refine ⟨2545398914833285556335841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787730439555428150228909 2545398914833285556335841)
                  ·
                    refine ⟨1909049186124964167251881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545398914833285556335841 1909049186124964167251881)
                    ·
                      refine ⟨1431786889593723125438911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909049186124964167251881 1431786889593723125438911)
                      ·
                        rfl

theorem cell23_2788395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 2, 2].length) (baseStart_2788395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788395 prefixEnd_2788395 := by exact prefixLift 2788395
  have htrace : WordTrace (prefixWord ++ tailWord_2788395) baseStart_2788395 baseEnd_2788395 := by
    simpa [prefixWord, tailWord_2788395, baseEnd_2788395] using wordTrace_append hprefix tailTrace_2788395
  have hstable : (prefixWord ++ tailWord_2788395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788395).length < 2 ^ (prefixWord ++ tailWord_2788395).sum := by decide
  have hdescent : baseEnd_2788395 < baseStart_2788395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788398 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2788398 : Nat := 118140960795 + 2788398 * 2 ^ 59
def prefixEnd_2788398 : Nat := 4983230072969 + 3 ^ 40 * 2788398 * 2
def baseEnd_2788398 : Nat := 1431788430035686613701397

theorem tailTrace_2788398 : CollatzResearch.WordTrace tailWord_2788398 prefixEnd_2788398 1431788430035686613701397 := by
  unfold tailWord_2788398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712653769014717663707731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67800820101411827539774565 12712653769014717663707731)
  ·
    refine ⟨19068980653522076495561597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12712653769014717663707731 19068980653522076495561597)
    ·
      refine ⟨7150867745070778685835599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19068980653522076495561597 7150867745070778685835599)
      ·
        refine ⟨10726301617606168028753399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150867745070778685835599 10726301617606168028753399)
        ·
          refine ⟨16089452426409252043130099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10726301617606168028753399 16089452426409252043130099)
          ·
            refine ⟨24134178639613878064695149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16089452426409252043130099 24134178639613878064695149)
            ·
              refine ⟨9050316989855204274260681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24134178639613878064695149 9050316989855204274260681)
              ·
                refine ⟨6787737742391403205695511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9050316989855204274260681 6787737742391403205695511)
                ·
                  refine ⟨10181606613587104808543267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787737742391403205695511 10181606613587104808543267)
                  ·
                    refine ⟨15272409920380657212814901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10181606613587104808543267 15272409920380657212814901)
                    ·
                      refine ⟨1431788430035686613701397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15272409920380657212814901 1431788430035686613701397)
                      ·
                        rfl

theorem cell23_2788398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2788398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788398 prefixEnd_2788398 := by exact prefixLift 2788398
  have htrace : WordTrace (prefixWord ++ tailWord_2788398) baseStart_2788398 baseEnd_2788398 := by
    simpa [prefixWord, tailWord_2788398, baseEnd_2788398] using wordTrace_append hprefix tailTrace_2788398
  have hstable : (prefixWord ++ tailWord_2788398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788398).length < 2 ^ (prefixWord ++ tailWord_2788398).sum := by decide
  have hdescent : baseEnd_2788398 < baseStart_2788398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788408 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_2788408 : Nat := 118140960795 + 2788408 * 2 ^ 59
def prefixEnd_2788408 : Nat := 4983230072969 + 3 ^ 40 * 2788408 * 2
def baseEnd_2788408 : Nat := 1431793564842231574576351

theorem tailTrace_2788408 : CollatzResearch.WordTrace tailWord_2788408 prefixEnd_2788408 1431793564842231574576351 := by
  unfold tailWord_2788408
  simp only [CollatzResearch.WordTrace]
  refine ⟨50850797441040756508762939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67801063254721008678350585 50850797441040756508762939)
  ·
    refine ⟨76276196161561134763144409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50850797441040756508762939 76276196161561134763144409)
    ·
      refine ⟨57207147121170851072358307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76276196161561134763144409 57207147121170851072358307)
      ·
        refine ⟨85810720681756276608537461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57207147121170851072358307 85810720681756276608537461)
        ·
          refine ⟨8044755063914650932050387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85810720681756276608537461 8044755063914650932050387)
          ·
            refine ⟨12067132595871976398075581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044755063914650932050387 12067132595871976398075581)
            ·
              refine ⟨4525174723451991149278343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12067132595871976398075581 4525174723451991149278343)
              ·
                refine ⟨6787762085177986723917515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525174723451991149278343 6787762085177986723917515)
                ·
                  refine ⟨10181643127766980085876273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787762085177986723917515 10181643127766980085876273)
                  ·
                    refine ⟨7636232345825235064407205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10181643127766980085876273 7636232345825235064407205)
                    ·
                      refine ⟨1431793564842231574576351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7636232345825235064407205 1431793564842231574576351)
                      ·
                        rfl

theorem cell23_2788408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_2788408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788408 prefixEnd_2788408 := by exact prefixLift 2788408
  have htrace : WordTrace (prefixWord ++ tailWord_2788408) baseStart_2788408 baseEnd_2788408 := by
    simpa [prefixWord, tailWord_2788408, baseEnd_2788408] using wordTrace_append hprefix tailTrace_2788408
  have hstable : (prefixWord ++ tailWord_2788408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788408).length < 2 ^ (prefixWord ++ tailWord_2788408).sum := by decide
  have hdescent : baseEnd_2788408 < baseStart_2788408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788446 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2788446 : Nat := 118140960795 + 2788446 * 2 ^ 59
def prefixEnd_2788446 : Nat := 4983230072969 + 3 ^ 40 * 2788446 * 2
def baseEnd_2788446 : Nat := 1431813077107102425901177

theorem tailTrace_2788446 : CollatzResearch.WordTrace tailWord_2788446 prefixEnd_2788446 1431813077107102425901177 := by
  unfold tailWord_2788446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712872606992980688426149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67801987237295897004939461 12712872606992980688426149)
  ·
    refine ⟨2383663613811183879079903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12712872606992980688426149 2383663613811183879079903)
    ·
      refine ⟨3575495420716775818619855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383663613811183879079903 3575495420716775818619855)
      ·
        refine ⟨5363243131075163727929783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575495420716775818619855 5363243131075163727929783)
        ·
          refine ⟨8044864696612745591894675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363243131075163727929783 8044864696612745591894675)
          ·
            refine ⟨12067297044919118387842013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044864696612745591894675 12067297044919118387842013)
            ·
              refine ⟨4525236391844669395440755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12067297044919118387842013 4525236391844669395440755)
              ·
                refine ⟨6787854587767004093161133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525236391844669395440755 6787854587767004093161133)
                ·
                  refine ⟨2545445470412626534935425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787854587767004093161133 2545445470412626534935425)
                  ·
                    refine ⟨1909084102809469901201569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545445470412626534935425 1909084102809469901201569)
                    ·
                      refine ⟨1431813077107102425901177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909084102809469901201569 1431813077107102425901177)
                      ·
                        rfl

theorem cell23_2788446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2788446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788446 prefixEnd_2788446 := by exact prefixLift 2788446
  have htrace : WordTrace (prefixWord ++ tailWord_2788446) baseStart_2788446 baseEnd_2788446 := by
    simpa [prefixWord, tailWord_2788446, baseEnd_2788446] using wordTrace_append hprefix tailTrace_2788446
  have hstable : (prefixWord ++ tailWord_2788446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788446).length < 2 ^ (prefixWord ++ tailWord_2788446).sum := by decide
  have hdescent : baseEnd_2788446 < baseStart_2788446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788451 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2788451 : Nat := 118140960795 + 2788451 * 2 ^ 59
def prefixEnd_2788451 : Nat := 4983230072969 + 3 ^ 40 * 2788451 * 2
def baseEnd_2788451 : Nat := 1431815644510374906338653

theorem tailTrace_2788451 : CollatzResearch.WordTrace tailWord_2788451 prefixEnd_2788451 1431815644510374906338653 := by
  unfold tailWord_2788451
  simp only [CollatzResearch.WordTrace]
  refine ⟨101703163220925731361341207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67802108813950487574227471 101703163220925731361341207)
  ·
    refine ⟨152554744831388597042011811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101703163220925731361341207 152554744831388597042011811)
    ·
      refine ⟨228832117247082895563017717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152554744831388597042011811 228832117247082895563017717)
      ·
        refine ⟨21453010991914021459032911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228832117247082895563017717 21453010991914021459032911)
        ·
          refine ⟨32179516487871032188549367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21453010991914021459032911 32179516487871032188549367)
          ·
            refine ⟨48269274731806548282824051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32179516487871032188549367 48269274731806548282824051)
            ·
              refine ⟨72403912097709822424236077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48269274731806548282824051 72403912097709822424236077)
              ·
                refine ⟨27151467036641183409088529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72403912097709822424236077 27151467036641183409088529)
                ·
                  refine ⟨20363600277480887556816397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27151467036641183409088529 20363600277480887556816397)
                  ·
                    refine ⟨7636350104055332833806149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20363600277480887556816397 7636350104055332833806149)
                    ·
                      refine ⟨1431815644510374906338653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7636350104055332833806149 1431815644510374906338653)
                      ·
                        rfl

theorem cell23_2788451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2788451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788451 prefixEnd_2788451 := by exact prefixLift 2788451
  have htrace : WordTrace (prefixWord ++ tailWord_2788451) baseStart_2788451 baseEnd_2788451 := by
    simpa [prefixWord, tailWord_2788451, baseEnd_2788451] using wordTrace_append hprefix tailTrace_2788451
  have hstable : (prefixWord ++ tailWord_2788451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788451).length < 2 ^ (prefixWord ++ tailWord_2788451).sum := by decide
  have hdescent : baseEnd_2788451 < baseStart_2788451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788456 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2788456 : Nat := 118140960795 + 2788456 * 2 ^ 59
def prefixEnd_2788456 : Nat := 4983230072969 + 3 ^ 40 * 2788456 * 2
def baseEnd_2788456 : Nat := 477272737304549128925377

theorem tailTrace_2788456 : CollatzResearch.WordTrace tailWord_2788456 prefixEnd_2788456 477272737304549128925377 := by
  unfold tailWord_2788456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50851672792953808607636611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67802230390605078143515481 50851672792953808607636611)
  ·
    refine ⟨76277509189430712911454917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50851672792953808607636611 76277509189430712911454917)
    ·
      refine ⟨14302032973018258670897797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76277509189430712911454917 14302032973018258670897797)
      ·
        refine ⟨2681631182440923500793337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14302032973018258670897797 2681631182440923500793337)
        ·
          refine ⟨2011223386830692625595003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2681631182440923500793337 2011223386830692625595003)
          ·
            refine ⟨3016835080246038938392505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011223386830692625595003 3016835080246038938392505)
            ·
              refine ⟨2262626310184529203794379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016835080246038938392505 2262626310184529203794379)
              ·
                refine ⟨3393939465276793805691569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262626310184529203794379 3393939465276793805691569)
                ·
                  refine ⟨2545454598957595354268677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393939465276793805691569 2545454598957595354268677)
                  ·
                    refine ⟨477272737304549128925377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545454598957595354268677 477272737304549128925377)
                    ·
                      rfl

theorem cell23_2788456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2788456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788456 prefixEnd_2788456 := by exact prefixLift 2788456
  have htrace : WordTrace (prefixWord ++ tailWord_2788456) baseStart_2788456 baseEnd_2788456 := by
    simpa [prefixWord, tailWord_2788456, baseEnd_2788456] using wordTrace_append hprefix tailTrace_2788456
  have hstable : (prefixWord ++ tailWord_2788456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788456).length < 2 ^ (prefixWord ++ tailWord_2788456).sum := by decide
  have hdescent : baseEnd_2788456 < baseStart_2788456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788462 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2788462 : Nat := 118140960795 + 2788462 * 2 ^ 59
def prefixEnd_2788462 : Nat := 4983230072969 + 3 ^ 40 * 2788462 * 2
def baseEnd_2788462 : Nat := 1431821292797574363301103

theorem tailTrace_2788462 : CollatzResearch.WordTrace tailWord_2788462 prefixEnd_2788462 1431821292797574363301103 := by
  unfold tailWord_2788462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712945552985735029998955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67802376282590586826661093 12712945552985735029998955)
  ·
    refine ⟨19069418329478602544998433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12712945552985735029998955 19069418329478602544998433)
    ·
      refine ⟨14302063747108951908748825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19069418329478602544998433 14302063747108951908748825)
      ·
        refine ⟨10726547810331713931561619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14302063747108951908748825 10726547810331713931561619)
        ·
          refine ⟨16089821715497570897342429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10726547810331713931561619 16089821715497570897342429)
          ·
            refine ⟨6033683143311589086503411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16089821715497570897342429 6033683143311589086503411)
            ·
              refine ⟨9050524714967383629755117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6033683143311589086503411 9050524714967383629755117)
              ·
                refine ⟨3393946768112768861158169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050524714967383629755117 3393946768112768861158169)
                ·
                  refine ⟨2545460076084576645868627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393946768112768861158169 2545460076084576645868627)
                  ·
                    refine ⟨3818190114126864968802941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2545460076084576645868627 3818190114126864968802941)
                    ·
                      refine ⟨1431821292797574363301103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3818190114126864968802941 1431821292797574363301103)
                      ·
                        rfl

theorem cell23_2788462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2788462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788462 prefixEnd_2788462 := by exact prefixLift 2788462
  have htrace : WordTrace (prefixWord ++ tailWord_2788462) baseStart_2788462 baseEnd_2788462 := by
    simpa [prefixWord, tailWord_2788462, baseEnd_2788462] using wordTrace_append hprefix tailTrace_2788462
  have hstable : (prefixWord ++ tailWord_2788462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788462).length < 2 ^ (prefixWord ++ tailWord_2788462).sum := by decide
  have hdescent : baseEnd_2788462 < baseStart_2788462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788471 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2788471 : Nat := 118140960795 + 2788471 * 2 ^ 59
def prefixEnd_2788471 : Nat := 4983230072969 + 3 ^ 40 * 2788471 * 2
def baseEnd_2788471 : Nat := 1431825914123464828088561

theorem tailTrace_2788471 : CollatzResearch.WordTrace tailWord_2788471 prefixEnd_2788471 1431825914123464828088561 := by
  unfold tailWord_2788471
  simp only [CollatzResearch.WordTrace]
  refine ⟨101703892680853274777069267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67802595120568849851379511 101703892680853274777069267)
  ·
    refine ⟨152555839021279912165603901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101703892680853274777069267 152555839021279912165603901)
    ·
      refine ⟨57208439632979967062101463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152555839021279912165603901 57208439632979967062101463)
      ·
        refine ⟨85812659449469950593152195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57208439632979967062101463 85812659449469950593152195)
        ·
          refine ⟨128718989174204925889728293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85812659449469950593152195 128718989174204925889728293)
          ·
            refine ⟨24134810470163423604324055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128718989174204925889728293 24134810470163423604324055)
            ·
              refine ⟨36202215705245135406486083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24134810470163423604324055 36202215705245135406486083)
              ·
                refine ⟨54303323557867703109729125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36202215705245135406486083 54303323557867703109729125)
                ·
                  refine ⟨10181873167100194333074211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54303323557867703109729125 10181873167100194333074211)
                  ·
                    refine ⟨15272809750650291499611317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10181873167100194333074211 15272809750650291499611317)
                    ·
                      refine ⟨1431825914123464828088561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15272809750650291499611317 1431825914123464828088561)
                      ·
                        rfl

theorem cell23_2788471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2788471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788471 prefixEnd_2788471 := by exact prefixLift 2788471
  have htrace : WordTrace (prefixWord ++ tailWord_2788471) baseStart_2788471 baseEnd_2788471 := by
    simpa [prefixWord, tailWord_2788471, baseEnd_2788471] using wordTrace_append hprefix tailTrace_2788471
  have hstable : (prefixWord ++ tailWord_2788471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788471).length < 2 ^ (prefixWord ++ tailWord_2788471).sum := by decide
  have hdescent : baseEnd_2788471 < baseStart_2788471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788519 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2788519 : Nat := 118140960795 + 2788519 * 2 ^ 59
def prefixEnd_2788519 : Nat := 4983230072969 + 3 ^ 40 * 2788519 * 2
def baseEnd_2788519 : Nat := 1431850561194880640288341

theorem tailTrace_2788519 : CollatzResearch.WordTrace tailWord_2788519 prefixEnd_2788519 1431850561194880640288341 := by
  unfold tailWord_2788519
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705643384679378974816611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67803762256452919316544407 101705643384679378974816611)
  ·
    refine ⟨152558465077019068462224917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101705643384679378974816611 152558465077019068462224917)
    ·
      refine ⟨7151178050485268834166793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152558465077019068462224917 7151178050485268834166793)
      ·
        refine ⟨5363383537863951625625095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151178050485268834166793 5363383537863951625625095)
        ·
          refine ⟨8045075306795927438437643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363383537863951625625095 8045075306795927438437643)
          ·
            refine ⟨12067612960193891157656465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045075306795927438437643 12067612960193891157656465)
            ·
              refine ⟨9050709720145418368242349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12067612960193891157656465 9050709720145418368242349)
              ·
                refine ⟨3394016145054531888090881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050709720145418368242349 3394016145054531888090881)
                ·
                  refine ⟨2545512108790898916068161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394016145054531888090881 2545512108790898916068161)
                  ·
                    refine ⟨1909134081593174187051121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545512108790898916068161 1909134081593174187051121)
                    ·
                      refine ⟨1431850561194880640288341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909134081593174187051121 1431850561194880640288341)
                      ·
                        rfl

theorem cell23_2788519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2788519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788519 prefixEnd_2788519 := by exact prefixLift 2788519
  have htrace : WordTrace (prefixWord ++ tailWord_2788519) baseStart_2788519 baseEnd_2788519 := by
    simpa [prefixWord, tailWord_2788519, baseEnd_2788519] using wordTrace_append hprefix tailTrace_2788519
  have hstable : (prefixWord ++ tailWord_2788519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788519).length < 2 ^ (prefixWord ++ tailWord_2788519).sum := by decide
  have hdescent : baseEnd_2788519 < baseStart_2788519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788525 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 7]
def baseStart_2788525 : Nat := 118140960795 + 2788525 * 2 ^ 59
def prefixEnd_2788525 : Nat := 4983230072969 + 3 ^ 40 * 2788525 * 2
def baseEnd_2788525 : Nat := 159094849119867512979257

theorem tailTrace_2788525 : CollatzResearch.WordTrace tailWord_2788525 prefixEnd_2788525 159094849119867512979257 := by
  unfold tailWord_2788525
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705862222657641999535029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67803908148438427999690019 101705862222657641999535029)
  ·
    refine ⟨9534924583374153937456409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101705862222657641999535029 9534924583374153937456409)
    ·
      refine ⟨7151193437530615453092307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9534924583374153937456409 7151193437530615453092307)
      ·
        refine ⟨10726790156295923179638461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7151193437530615453092307 10726790156295923179638461)
        ·
          refine ⟨4022546308610971192364423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10726790156295923179638461 4022546308610971192364423)
          ·
            refine ⟨6033819462916456788546635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022546308610971192364423 6033819462916456788546635)
            ·
              refine ⟨9050729194374685182819953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6033819462916456788546635 9050729194374685182819953)
              ·
                refine ⟨6788046895781013887114965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9050729194374685182819953 6788046895781013887114965)
                ·
                  refine ⟨159094849119867512979257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6788046895781013887114965 159094849119867512979257)
                  ·
                    rfl

theorem cell23_2788525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_2788525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788525 prefixEnd_2788525 := by exact prefixLift 2788525
  have htrace : WordTrace (prefixWord ++ tailWord_2788525) baseStart_2788525 baseEnd_2788525 := by
    simpa [prefixWord, tailWord_2788525, baseEnd_2788525] using wordTrace_append hprefix tailTrace_2788525
  have hstable : (prefixWord ++ tailWord_2788525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788525).length < 2 ^ (prefixWord ++ tailWord_2788525).sum := by decide
  have hdescent : baseEnd_2788525 < baseStart_2788525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788531 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2788531 : Nat := 118140960795 + 2788531 * 2 ^ 59
def prefixEnd_2788531 : Nat := 4983230072969 + 3 ^ 40 * 2788531 * 2
def baseEnd_2788531 : Nat := 1431856722962734593338285

theorem tailTrace_2788531 : CollatzResearch.WordTrace tailWord_2788531 prefixEnd_2788531 1431856722962734593338285 := by
  unfold tailWord_2788531
  simp only [CollatzResearch.WordTrace]
  refine ⟨101706081060635905024253447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67804054040423936682835631 101706081060635905024253447)
  ·
    refine ⟨152559121590953857536380171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101706081060635905024253447 152559121590953857536380171)
    ·
      refine ⟨228838682386430786304570257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152559121590953857536380171 228838682386430786304570257)
      ·
        refine ⟨171629011789823089728427693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228838682386430786304570257 171629011789823089728427693)
        ·
          refine ⟨64360879421183658648160385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171629011789823089728427693 64360879421183658648160385)
          ·
            refine ⟨48270659565887743986120289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64360879421183658648160385 48270659565887743986120289)
            ·
              refine ⟨36202994674415807989590217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48270659565887743986120289 36202994674415807989590217)
              ·
                refine ⟨27152246005811855992192663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36202994674415807989590217 27152246005811855992192663)
                ·
                  refine ⟨40728369008717783988288995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27152246005811855992192663 40728369008717783988288995)
                  ·
                    refine ⟨61092553513076675982433493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40728369008717783988288995 61092553513076675982433493)
                    ·
                      refine ⟨1431856722962734593338285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61092553513076675982433493 1431856722962734593338285)
                      ·
                        rfl

theorem cell23_2788531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2788531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788531 prefixEnd_2788531 := by exact prefixLift 2788531
  have htrace : WordTrace (prefixWord ++ tailWord_2788531) baseStart_2788531 baseEnd_2788531 := by
    simpa [prefixWord, tailWord_2788531, baseEnd_2788531] using wordTrace_append hprefix tailTrace_2788531
  have hstable : (prefixWord ++ tailWord_2788531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788531).length < 2 ^ (prefixWord ++ tailWord_2788531).sum := by decide
  have hdescent : baseEnd_2788531 < baseStart_2788531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788542 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2788542 : Nat := 118140960795 + 2788542 * 2 ^ 59
def prefixEnd_2788542 : Nat := 4983230072969 + 3 ^ 40 * 2788542 * 2
def baseEnd_2788542 : Nat := 159095819027770450033415

theorem tailTrace_2788542 : CollatzResearch.WordTrace tailWord_2788542 prefixEnd_2788542 159095819027770450033415 := by
  unfold tailWord_2788542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713310282949506737862985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67804321509064035935269253 12713310282949506737862985)
  ·
    refine ⟨9534982712212130053397239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12713310282949506737862985 9534982712212130053397239)
    ·
      refine ⟨14302474068318195080095859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534982712212130053397239 14302474068318195080095859)
      ·
        refine ⟨21453711102477292620143789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302474068318195080095859 21453711102477292620143789)
        ·
          refine ⟨8045141663428984732553921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21453711102477292620143789 8045141663428984732553921)
          ·
            refine ⟨6033856247571738549415441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045141663428984732553921 6033856247571738549415441)
            ·
              refine ⟨4525392185678803912061581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033856247571738549415441 4525392185678803912061581)
              ·
                refine ⟨1697022069629551467023093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4525392185678803912061581 1697022069629551467023093)
                ·
                  refine ⟨159095819027770450033415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697022069629551467023093 159095819027770450033415)
                  ·
                    rfl

theorem cell23_2788542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2788542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788542 prefixEnd_2788542 := by exact prefixLift 2788542
  have htrace : WordTrace (prefixWord ++ tailWord_2788542) baseStart_2788542 baseEnd_2788542 := by
    simpa [prefixWord, tailWord_2788542, baseEnd_2788542] using wordTrace_append hprefix tailTrace_2788542
  have hstable : (prefixWord ++ tailWord_2788542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788542).length < 2 ^ (prefixWord ++ tailWord_2788542).sum := by decide
  have hdescent : baseEnd_2788542 < baseStart_2788542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788551 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 10]
def baseStart_2788551 : Nat := 118140960795 + 2788551 * 2 ^ 59
def prefixEnd_2788551 : Nat := 4983230072969 + 3 ^ 40 * 2788551 * 2
def baseEnd_2788551 : Nat := 477288997525274838362731

theorem tailTrace_2788551 : CollatzResearch.WordTrace tailWord_2788551 prefixEnd_2788551 477288997525274838362731 := by
  unfold tailWord_2788551
  simp only [CollatzResearch.WordTrace]
  refine ⟨101706810520563448439981507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67804540347042298959987671 101706810520563448439981507)
  ·
    refine ⟨152560215780845172659972261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101706810520563448439981507 152560215780845172659972261)
    ·
      refine ⟨28605040458908469873744799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152560215780845172659972261 28605040458908469873744799)
      ·
        refine ⟨42907560688362704810617199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28605040458908469873744799 42907560688362704810617199)
        ·
          refine ⟨64361341032544057215925799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42907560688362704810617199 64361341032544057215925799)
          ·
            refine ⟨96542011548816085823888699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64361341032544057215925799 96542011548816085823888699)
            ·
              refine ⟨144813017323224128735833049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96542011548816085823888699 144813017323224128735833049)
              ·
                refine ⟨108609762992418096551874787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144813017323224128735833049 108609762992418096551874787)
                ·
                  refine ⟨162914644488627144827812181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108609762992418096551874787 162914644488627144827812181)
                  ·
                    refine ⟨477288997525274838362731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 162914644488627144827812181 477288997525274838362731)
                    ·
                      rfl

theorem cell23_2788551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_2788551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788551 prefixEnd_2788551 := by exact prefixLift 2788551
  have htrace : WordTrace (prefixWord ++ tailWord_2788551) baseStart_2788551 baseEnd_2788551 := by
    simpa [prefixWord, tailWord_2788551, baseEnd_2788551] using wordTrace_append hprefix tailTrace_2788551
  have hstable : (prefixWord ++ tailWord_2788551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788551).length < 2 ^ (prefixWord ++ tailWord_2788551).sum := by decide
  have hdescent : baseEnd_2788551 < baseStart_2788551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_2788571 : Nat := 118140960795 + 2788571 * 2 ^ 59
def prefixEnd_2788571 : Nat := 4983230072969 + 3 ^ 40 * 2788571 * 2
def baseEnd_2788571 : Nat := 1431877262188914436838101

theorem tailTrace_2788571 : CollatzResearch.WordTrace tailWord_2788571 prefixEnd_2788571 1431877262188914436838101 := by
  unfold tailWord_2788571
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707539980490991855709567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67805026653660661237139711 101707539980490991855709567)
  ·
    refine ⟨152561309970736487783564351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101707539980490991855709567 152561309970736487783564351)
    ·
      refine ⟨228841964956104731675346527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152561309970736487783564351 228841964956104731675346527)
      ·
        refine ⟨343262947434157097513019791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228841964956104731675346527 343262947434157097513019791)
        ·
          refine ⟨514894421151235646269529687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343262947434157097513019791 514894421151235646269529687)
          ·
            refine ⟨772341631726853469404294531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514894421151235646269529687 772341631726853469404294531)
            ·
              refine ⟨1158512447590280204106441797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772341631726853469404294531 1158512447590280204106441797)
              ·
                refine ⟨217221083923177538269957837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1158512447590280204106441797 217221083923177538269957837)
                ·
                  refine ⟨81457906471191576851234189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217221083923177538269957837 81457906471191576851234189)
                  ·
                    refine ⟨30546714926696841319212821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81457906471191576851234189 30546714926696841319212821)
                    ·
                      refine ⟨1431877262188914436838101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30546714926696841319212821 1431877262188914436838101)
                      ·
                        rfl

theorem cell23_2788571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_2788571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788571 prefixEnd_2788571 := by exact prefixLift 2788571
  have htrace : WordTrace (prefixWord ++ tailWord_2788571) baseStart_2788571 baseEnd_2788571 := by
    simpa [prefixWord, tailWord_2788571, baseEnd_2788571] using wordTrace_append hprefix tailTrace_2788571
  have hstable : (prefixWord ++ tailWord_2788571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788571).length < 2 ^ (prefixWord ++ tailWord_2788571).sum := by decide
  have hdescent : baseEnd_2788571 < baseStart_2788571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788575 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 4, 2]
def baseStart_2788575 : Nat := 118140960795 + 2788575 * 2 ^ 59
def prefixEnd_2788575 : Nat := 4983230072969 + 3 ^ 40 * 2788575 * 2
def baseEnd_2788575 : Nat := 1431879316111532421188083

theorem tailTrace_2788575 : CollatzResearch.WordTrace tailWord_2788575 prefixEnd_2788575 1431879316111532421188083 := by
  unfold tailWord_2788575
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707685872476500538855179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67805123914984333692570119 101707685872476500538855179)
  ·
    refine ⟨152561528808714750808282769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101707685872476500538855179 152561528808714750808282769)
    ·
      refine ⟨114421146606536063106212077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152561528808714750808282769 114421146606536063106212077)
      ·
        refine ⟨42907929977451023664829529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114421146606536063106212077 42907929977451023664829529)
        ·
          refine ⟨32180947483088267748622147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42907929977451023664829529 32180947483088267748622147)
          ·
            refine ⟨48271421224632401622933221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32180947483088267748622147 48271421224632401622933221)
            ·
              refine ⟨9050891479618575304299979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48271421224632401622933221 9050891479618575304299979)
              ·
                refine ⟨13576337219427862956449969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9050891479618575304299979 13576337219427862956449969)
                ·
                  refine ⟨10182252914570897217337477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13576337219427862956449969 10182252914570897217337477)
                  ·
                    refine ⟨1909172421482043228250777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10182252914570897217337477 1909172421482043228250777)
                    ·
                      refine ⟨1431879316111532421188083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909172421482043228250777 1431879316111532421188083)
                      ·
                        rfl

theorem cell23_2788575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_2788575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788575 prefixEnd_2788575 := by exact prefixLift 2788575
  have htrace : WordTrace (prefixWord ++ tailWord_2788575) baseStart_2788575 baseEnd_2788575 := by
    simpa [prefixWord, tailWord_2788575, baseEnd_2788575] using wordTrace_append hprefix tailTrace_2788575
  have hstable : (prefixWord ++ tailWord_2788575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788575).length < 2 ^ (prefixWord ++ tailWord_2788575).sum := by decide
  have hdescent : baseEnd_2788575 < baseStart_2788575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788612 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2788612 : Nat := 118140960795 + 2788612 * 2 ^ 59
def prefixEnd_2788612 : Nat := 4983230072969 + 3 ^ 40 * 2788612 * 2
def baseEnd_2788612 : Nat := 1431898314895748776425413

theorem tailTrace_2788612 : CollatzResearch.WordTrace tailWord_2788612 prefixEnd_2788612 1431898314895748776425413 := by
  unfold tailWord_2788612
  simp only [CollatzResearch.WordTrace]
  refine ⟨50854517686671227928976045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67806023582228303905301393 50854517686671227928976045)
  ·
    refine ⟨19070444132501710473366017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50854517686671227928976045 19070444132501710473366017)
    ·
      refine ⟨14302833099376282855024513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19070444132501710473366017 14302833099376282855024513)
      ·
        refine ⟨10727124824532212141268385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14302833099376282855024513 10727124824532212141268385)
        ·
          refine ⟨8045343618399159105951289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10727124824532212141268385 8045343618399159105951289)
          ·
            refine ⟨6034007713799369329463467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045343618399159105951289 6034007713799369329463467)
            ·
              refine ⟨9051011570699053994195201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034007713799369329463467 9051011570699053994195201)
              ·
                refine ⟨6788258678024290495646401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9051011570699053994195201 6788258678024290495646401)
                ·
                  refine ⟨5091194008518217871734801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788258678024290495646401 5091194008518217871734801)
                  ·
                    refine ⟨3818395506388663403801101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091194008518217871734801 3818395506388663403801101)
                    ·
                      refine ⟨1431898314895748776425413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3818395506388663403801101 1431898314895748776425413)
                      ·
                        rfl

theorem cell23_2788612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2788612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788612 prefixEnd_2788612 := by exact prefixLift 2788612
  have htrace : WordTrace (prefixWord ++ tailWord_2788612) baseStart_2788612 baseEnd_2788612 := by
    simpa [prefixWord, tailWord_2788612, baseEnd_2788612] using wordTrace_append hprefix tailTrace_2788612
  have hstable : (prefixWord ++ tailWord_2788612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788612).length < 2 ^ (prefixWord ++ tailWord_2788612).sum := by decide
  have hdescent : baseEnd_2788612 < baseStart_2788612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788619 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 1, 4]
def baseStart_2788619 : Nat := 118140960795 + 2788619 * 2 ^ 59
def prefixEnd_2788619 : Nat := 4983230072969 + 3 ^ 40 * 2788619 * 2
def baseEnd_2788619 : Nat := 477300636420110083012627

theorem tailTrace_2788619 : CollatzResearch.WordTrace tailWord_2788619 prefixEnd_2788619 477300636420110083012627 := by
  unfold tailWord_2788619
  simp only [CollatzResearch.WordTrace]
  refine ⟨101709290684317096053456911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67806193789544730702304607 101709290684317096053456911)
  ·
    refine ⟨152563936026475644080185367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101709290684317096053456911 152563936026475644080185367)
    ·
      refine ⟨228845904039713466120278051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152563936026475644080185367 228845904039713466120278051)
      ·
        refine ⟨343268856059570199180417077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228845904039713466120278051 343268856059570199180417077)
        ·
          refine ⟨32181455255584706173164101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343268856059570199180417077 32181455255584706173164101)
          ·
            refine ⟨6034022860422132407468269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32181455255584706173164101 6034022860422132407468269)
            ·
              refine ⟨2262758572658299652800601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034022860422132407468269 2262758572658299652800601)
              ·
                refine ⟨1697068929493724739600451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2262758572658299652800601 1697068929493724739600451)
                ·
                  refine ⟨2545603394240587109400677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697068929493724739600451 2545603394240587109400677)
                  ·
                    refine ⟨477300636420110083012627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545603394240587109400677 477300636420110083012627)
                    ·
                      rfl

theorem cell23_2788619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 4].length) (baseStart_2788619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788619 prefixEnd_2788619 := by exact prefixLift 2788619
  have htrace : WordTrace (prefixWord ++ tailWord_2788619) baseStart_2788619 baseEnd_2788619 := by
    simpa [prefixWord, tailWord_2788619, baseEnd_2788619] using wordTrace_append hprefix tailTrace_2788619
  have hstable : (prefixWord ++ tailWord_2788619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788619).length < 2 ^ (prefixWord ++ tailWord_2788619).sum := by decide
  have hdescent : baseEnd_2788619 < baseStart_2788619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788632 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 6]
def baseStart_2788632 : Nat := 118140960795 + 2788632 * 2 ^ 59
def prefixEnd_2788632 : Nat := 4983230072969 + 3 ^ 40 * 2788632 * 2
def baseEnd_2788632 : Nat := 159100953834315410908369

theorem tailTrace_2788632 : CollatzResearch.WordTrace tailWord_2788632 prefixEnd_2788632 159100953834315410908369 := by
  unfold tailWord_2788632
  simp only [CollatzResearch.WordTrace]
  refine ⟨50854882416634999636840075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67806509888846666182453433 50854882416634999636840075)
  ·
    refine ⟨76282323624952499455260113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50854882416634999636840075 76282323624952499455260113)
    ·
      refine ⟨57211742718714374591445085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76282323624952499455260113 57211742718714374591445085)
      ·
        refine ⟨21454403519517890471791907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57211742718714374591445085 21454403519517890471791907)
        ·
          refine ⟨32181605279276835707687861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21454403519517890471791907 32181605279276835707687861)
          ·
            refine ⟨3017025494932203347595737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32181605279276835707687861 3017025494932203347595737)
            ·
              refine ⟨2262769121199152510696803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017025494932203347595737 2262769121199152510696803)
              ·
                refine ⟨3394153681798728766045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262769121199152510696803 3394153681798728766045205)
                ·
                  refine ⟨159100953834315410908369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3394153681798728766045205 159100953834315410908369)
                  ·
                    rfl

theorem cell23_2788632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_2788632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788632 prefixEnd_2788632 := by exact prefixLift 2788632
  have htrace : WordTrace (prefixWord ++ tailWord_2788632) baseStart_2788632 baseEnd_2788632 := by
    simpa [prefixWord, tailWord_2788632, baseEnd_2788632] using wordTrace_append hprefix tailTrace_2788632
  have hstable : (prefixWord ++ tailWord_2788632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788632).length < 2 ^ (prefixWord ++ tailWord_2788632).sum := by decide
  have hdescent : baseEnd_2788632 < baseStart_2788632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788635 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 6, 3, 2]
def baseStart_2788635 : Nat := 118140960795 + 2788635 * 2 ^ 59
def prefixEnd_2788635 : Nat := 4983230072969 + 3 ^ 40 * 2788635 * 2
def baseEnd_2788635 : Nat := 1431910124950802186437807

theorem tailTrace_2788635 : CollatzResearch.WordTrace tailWord_2788635 prefixEnd_2788635 1431910124950802186437807 := by
  unfold tailWord_2788635
  simp only [CollatzResearch.WordTrace]
  refine ⟨101709874252259130786039359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67806582834839420524026239 101709874252259130786039359)
  ·
    refine ⟨152564811378388696179059039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101709874252259130786039359 152564811378388696179059039)
    ·
      refine ⟨228847217067583044268588559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152564811378388696179059039 228847217067583044268588559)
      ·
        refine ⟨343270825601374566402882839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228847217067583044268588559 343270825601374566402882839)
        ·
          refine ⟨514906238402061849604324259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343270825601374566402882839 514906238402061849604324259)
          ·
            refine ⟨772359357603092774406486389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514906238402061849604324259 772359357603092774406486389)
            ·
              refine ⟨72408689775289947600608099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 772359357603092774406486389 72408689775289947600608099)
              ·
                refine ⟨108613034662934921400912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72408689775289947600608099 108613034662934921400912149)
                ·
                  refine ⟨5091235999825074440667757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108613034662934921400912149 5091235999825074440667757)
                  ·
                    refine ⟨1909213499934402915250409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091235999825074440667757 1909213499934402915250409)
                    ·
                      refine ⟨1431910124950802186437807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909213499934402915250409 1431910124950802186437807)
                      ·
                        rfl

theorem cell23_2788635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 3, 2].length) (baseStart_2788635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788635 prefixEnd_2788635 := by exact prefixLift 2788635
  have htrace : WordTrace (prefixWord ++ tailWord_2788635) baseStart_2788635 baseEnd_2788635 := by
    simpa [prefixWord, tailWord_2788635, baseEnd_2788635] using wordTrace_append hprefix tailTrace_2788635
  have hstable : (prefixWord ++ tailWord_2788635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788635).length < 2 ^ (prefixWord ++ tailWord_2788635).sum := by decide
  have hdescent : baseEnd_2788635 < baseStart_2788635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788645 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_2788645 : Nat := 118140960795 + 2788645 * 2 ^ 59
def prefixEnd_2788645 : Nat := 4983230072969 + 3 ^ 40 * 2788645 * 2
def baseEnd_2788645 : Nat := 477305086585782382437587

theorem tailTrace_2788645 : CollatzResearch.WordTrace tailWord_2788645 prefixEnd_2788645 477305086585782382437587 := by
  unfold tailWord_2788645
  simp only [CollatzResearch.WordTrace]
  refine ⟨101710238982222902493903389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67806825988148601662602259 101710238982222902493903389)
  ·
    refine ⟨38141339618333588435213771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101710238982222902493903389 38141339618333588435213771)
    ·
      refine ⟨57212009427500382652820657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38141339618333588435213771 57212009427500382652820657)
      ·
        refine ⟨42909007070625286989615493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57212009427500382652820657 42909007070625286989615493)
        ·
          refine ⟨8045438825742241310552905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42909007070625286989615493 8045438825742241310552905)
          ·
            refine ⟨6034079119306680982914679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045438825742241310552905 6034079119306680982914679)
            ·
              refine ⟨9051118678960021474372019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034079119306680982914679 9051118678960021474372019)
              ·
                refine ⟨13576678018440032211558029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051118678960021474372019 13576678018440032211558029)
                ·
                  refine ⟨5091254256915012079334261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13576678018440032211558029 5091254256915012079334261)
                  ·
                    refine ⟨477305086585782382437587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5091254256915012079334261 477305086585782382437587)
                    ·
                      rfl

theorem cell23_2788645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_2788645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788645 prefixEnd_2788645 := by exact prefixLift 2788645
  have htrace : WordTrace (prefixWord ++ tailWord_2788645) baseStart_2788645 baseEnd_2788645 := by
    simpa [prefixWord, tailWord_2788645, baseEnd_2788645] using wordTrace_append hprefix tailTrace_2788645
  have hstable : (prefixWord ++ tailWord_2788645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788645).length < 2 ^ (prefixWord ++ tailWord_2788645).sum := by decide
  have hdescent : baseEnd_2788645 < baseStart_2788645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788682 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_2788682 : Nat := 118140960795 + 2788682 * 2 ^ 59
def prefixEnd_2788682 : Nat := 4983230072969 + 3 ^ 40 * 2788682 * 2
def baseEnd_2788682 : Nat := 1431934258541563502550091

theorem tailTrace_2788682 : CollatzResearch.WordTrace tailWord_2788682 prefixEnd_2788682 1431934258541563502550091 := by
  unfold tailWord_2788682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427897120772214453250075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67807725655392571875333533 25427897120772214453250075)
  ·
    refine ⟨38141845681158321679875113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25427897120772214453250075 38141845681158321679875113)
    ·
      refine ⟨28606384260868741259906335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38141845681158321679875113 28606384260868741259906335)
      ·
        refine ⟨42909576391303111889859503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28606384260868741259906335 42909576391303111889859503)
        ·
          refine ⟨64364364586954667834789255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42909576391303111889859503 64364364586954667834789255)
          ·
            refine ⟨96546546880432001752183883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64364364586954667834789255 96546546880432001752183883)
            ·
              refine ⟨144819820320648002628275825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96546546880432001752183883 144819820320648002628275825)
              ·
                refine ⟨108614865240486001971206869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144819820320648002628275825 108614865240486001971206869)
                ·
                  refine ⟨2545660904073890671200161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108614865240486001971206869 2545660904073890671200161)
                  ·
                    refine ⟨1909245678055418003400121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545660904073890671200161 1909245678055418003400121)
                    ·
                      refine ⟨1431934258541563502550091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909245678055418003400121 1431934258541563502550091)
                      ·
                        rfl

theorem cell23_2788682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_2788682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788682 prefixEnd_2788682 := by exact prefixLift 2788682
  have htrace : WordTrace (prefixWord ++ tailWord_2788682) baseStart_2788682 baseEnd_2788682 := by
    simpa [prefixWord, tailWord_2788682, baseEnd_2788682] using wordTrace_append hprefix tailTrace_2788682
  have hstable : (prefixWord ++ tailWord_2788682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788682).length < 2 ^ (prefixWord ++ tailWord_2788682).sum := by decide
  have hdescent : baseEnd_2788682 < baseStart_2788682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788692 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_2788692 : Nat := 118140960795 + 2788692 * 2 ^ 59
def prefixEnd_2788692 : Nat := 4983230072969 + 3 ^ 40 * 2788692 * 2
def baseEnd_2788692 : Nat := 477313131116036154475015

theorem tailTrace_2788692 : CollatzResearch.WordTrace tailWord_2788692 prefixEnd_2788692 477313131116036154475015 := by
  unfold tailWord_2788692
  simp only [CollatzResearch.WordTrace]
  refine ⟨50855976606526314760432165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67807968808701753013909553 50855976606526314760432165)
  ·
    refine ⟨9535495613723684017581031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50855976606526314760432165 9535495613723684017581031)
    ·
      refine ⟨14303243420585526026371547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535495613723684017581031 14303243420585526026371547)
      ·
        refine ⟨21454865130878289039557321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14303243420585526026371547 21454865130878289039557321)
        ·
          refine ⟨16091148848158716779667991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21454865130878289039557321 16091148848158716779667991)
          ·
            refine ⟨24136723272238075169501987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16091148848158716779667991 24136723272238075169501987)
            ·
              refine ⟨36205084908357112754252981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24136723272238075169501987 36205084908357112754252981)
              ·
                refine ⟨3394226710158479320711217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36205084908357112754252981 3394226710158479320711217)
                ·
                  refine ⟨2545670032618859490533413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394226710158479320711217 2545670032618859490533413)
                  ·
                    refine ⟨477313131116036154475015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545670032618859490533413 477313131116036154475015)
                    ·
                      rfl

theorem cell23_2788692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_2788692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788692 prefixEnd_2788692 := by exact prefixLift 2788692
  have htrace : WordTrace (prefixWord ++ tailWord_2788692) baseStart_2788692 baseEnd_2788692 := by
    simpa [prefixWord, tailWord_2788692, baseEnd_2788692] using wordTrace_append hprefix tailTrace_2788692
  have hstable : (prefixWord ++ tailWord_2788692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788692).length < 2 ^ (prefixWord ++ tailWord_2788692).sum := by decide
  have hdescent : baseEnd_2788692 < baseStart_2788692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788695 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2788695 : Nat := 118140960795 + 2788695 * 2 ^ 59
def prefixEnd_2788695 : Nat := 4983230072969 + 3 ^ 40 * 2788695 * 2
def baseEnd_2788695 : Nat := 1431940933790071951687531

theorem tailTrace_2788695 : CollatzResearch.WordTrace tailWord_2788695 prefixEnd_2788695 1431940933790071951687531 := by
  unfold tailWord_2788695
  simp only [CollatzResearch.WordTrace]
  refine ⟨101712062632041761033223539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67808041754694507355482359 101712062632041761033223539)
  ·
    refine ⟨152568093948062641549835309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101712062632041761033223539 152568093948062641549835309)
    ·
      refine ⟨57213035230523490581188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152568093948062641549835309 57213035230523490581188241)
      ·
        refine ⟨42909776422892617935891181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57213035230523490581188241 42909776422892617935891181)
        ·
          refine ⟨16091166158584731725959193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42909776422892617935891181 16091166158584731725959193)
          ·
            refine ⟨12068374618938548794469395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16091166158584731725959193 12068374618938548794469395)
            ·
              refine ⟨18102561928407823191704093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12068374618938548794469395 18102561928407823191704093)
              ·
                refine ⟨6788460723152933696889035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18102561928407823191704093 6788460723152933696889035)
                ·
                  refine ⟨10182691084729400545333553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788460723152933696889035 10182691084729400545333553)
                  ·
                    refine ⟨7637018313547050409000165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10182691084729400545333553 7637018313547050409000165)
                    ·
                      refine ⟨1431940933790071951687531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7637018313547050409000165 1431940933790071951687531)
                      ·
                        rfl

theorem cell23_2788695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2788695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788695 prefixEnd_2788695 := by exact prefixLift 2788695
  have htrace : WordTrace (prefixWord ++ tailWord_2788695) baseStart_2788695 baseEnd_2788695 := by
    simpa [prefixWord, tailWord_2788695, baseEnd_2788695] using wordTrace_append hprefix tailTrace_2788695
  have hstable : (prefixWord ++ tailWord_2788695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788695).length < 2 ^ (prefixWord ++ tailWord_2788695).sum := by decide
  have hdescent : baseEnd_2788695 < baseStart_2788695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788716 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_2788716 : Nat := 118140960795 + 2788716 * 2 ^ 59
def prefixEnd_2788716 : Nat := 4983230072969 + 3 ^ 40 * 2788716 * 2
def baseEnd_2788716 : Nat := 1431951716883816369524935

theorem tailTrace_2788716 : CollatzResearch.WordTrace tailWord_2788716 prefixEnd_2788716 1431951716883816369524935 := by
  unfold tailWord_2788716
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856414282482840809869001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67808552376643787746492001 50856414282482840809869001)
  ·
    refine ⟨38142310711862130607401751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50856414282482840809869001 38142310711862130607401751)
    ·
      refine ⟨57213466067793195911102627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38142310711862130607401751 57213466067793195911102627)
      ·
        refine ⟨85820199101689793866653941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57213466067793195911102627 85820199101689793866653941)
        ·
          refine ⟨8045643665783418174998807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85820199101689793866653941 8045643665783418174998807)
          ·
            refine ⟨12068465498675127262498211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045643665783418174998807 12068465498675127262498211)
            ·
              refine ⟨18102698248012690893747317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12068465498675127262498211 18102698248012690893747317)
              ·
                refine ⟨1697127960751189771288811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18102698248012690893747317 1697127960751189771288811)
                ·
                  refine ⟨2545691941126784656933217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697127960751189771288811 2545691941126784656933217)
                  ·
                    refine ⟨1909268955845088492699913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545691941126784656933217 1909268955845088492699913)
                    ·
                      refine ⟨1431951716883816369524935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909268955845088492699913 1431951716883816369524935)
                      ·
                        rfl

theorem cell23_2788716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_2788716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788716 prefixEnd_2788716 := by exact prefixLift 2788716
  have htrace : WordTrace (prefixWord ++ tailWord_2788716) baseStart_2788716 baseEnd_2788716 := by
    simpa [prefixWord, tailWord_2788716, baseEnd_2788716] using wordTrace_append hprefix tailTrace_2788716
  have hstable : (prefixWord ++ tailWord_2788716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788716).length < 2 ^ (prefixWord ++ tailWord_2788716).sum := by decide
  have hdescent : baseEnd_2788716 < baseStart_2788716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788732 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2788732 : Nat := 118140960795 + 2788732 * 2 ^ 59
def prefixEnd_2788732 : Nat := 4983230072969 + 3 ^ 40 * 2788732 * 2
def baseEnd_2788732 : Nat := 1431959932574288306924861

theorem tailTrace_2788732 : CollatzResearch.WordTrace tailWord_2788732 prefixEnd_2788732 1431959932574288306924861 := by
  unfold tailWord_2788732
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856706066453858176160225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67808941421938477568213633 50856706066453858176160225)
  ·
    refine ⟨38142529549840393632120169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50856706066453858176160225 38142529549840393632120169)
    ·
      refine ⟨28606897162380295224090127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38142529549840393632120169 28606897162380295224090127)
      ·
        refine ⟨42910345743570442836135191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28606897162380295224090127 42910345743570442836135191)
        ·
          refine ⟨64365518615355664254202787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42910345743570442836135191 64365518615355664254202787)
          ·
            refine ⟨96548277923033496381304181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64365518615355664254202787 96548277923033496381304181)
            ·
              refine ⟨9051401055284390285747267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96548277923033496381304181 9051401055284390285747267)
              ·
                refine ⟨13577101582926585428620901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051401055284390285747267 13577101582926585428620901)
                ·
                  refine ⟨2545706546798734767866419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13577101582926585428620901 2545706546798734767866419)
                  ·
                    refine ⟨3818559820198102151799629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2545706546798734767866419 3818559820198102151799629)
                    ·
                      refine ⟨1431959932574288306924861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3818559820198102151799629 1431959932574288306924861)
                      ·
                        rfl

theorem cell23_2788732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2788732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788732 prefixEnd_2788732 := by exact prefixLift 2788732
  have htrace : WordTrace (prefixWord ++ tailWord_2788732) baseStart_2788732 baseEnd_2788732 := by
    simpa [prefixWord, tailWord_2788732, baseEnd_2788732] using wordTrace_append hprefix tailTrace_2788732
  have hstable : (prefixWord ++ tailWord_2788732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788732).length < 2 ^ (prefixWord ++ tailWord_2788732).sum := by decide
  have hdescent : baseEnd_2788732 < baseStart_2788732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_2788772 : Nat := 118140960795 + 2788772 * 2 ^ 59
def prefixEnd_2788772 : Nat := 4983230072969 + 3 ^ 40 * 2788772 * 2
def baseEnd_2788772 : Nat := 1431980471800468150424677

theorem tailTrace_2788772 : CollatzResearch.WordTrace tailWord_2788772 prefixEnd_2788772 1431980471800468150424677 := by
  unfold tailWord_2788772
  simp only [CollatzResearch.WordTrace]
  refine ⟨50857435526381401591888285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67809914035175202122517713 50857435526381401591888285)
  ·
    refine ⟨19071538322393025596958107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50857435526381401591888285 19071538322393025596958107)
    ·
      refine ⟨28607307483589538395437161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19071538322393025596958107 28607307483589538395437161)
      ·
        refine ⟨21455480612692153796577871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28607307483589538395437161 21455480612692153796577871)
        ·
          refine ⟨32183220919038230694866807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21455480612692153796577871 32183220919038230694866807)
          ·
            refine ⟨48274831378557346042300211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32183220919038230694866807 48274831378557346042300211)
            ·
              refine ⟨72412247067836019063450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48274831378557346042300211 72412247067836019063450317)
              ·
                refine ⟨27154592650438507148793869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72412247067836019063450317 27154592650438507148793869)
                ·
                  refine ⟨10182972243914440180797701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27154592650438507148793869 10182972243914440180797701)
                  ·
                    refine ⟨1909307295733957533899569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10182972243914440180797701 1909307295733957533899569)
                    ·
                      refine ⟨1431980471800468150424677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909307295733957533899569 1431980471800468150424677)
                      ·
                        rfl

theorem cell23_2788772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_2788772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788772 prefixEnd_2788772 := by exact prefixLift 2788772
  have htrace : WordTrace (prefixWord ++ tailWord_2788772) baseStart_2788772 baseEnd_2788772 := by
    simpa [prefixWord, tailWord_2788772, baseEnd_2788772] using wordTrace_append hprefix tailTrace_2788772
  have hstable : (prefixWord ++ tailWord_2788772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788772).length < 2 ^ (prefixWord ++ tailWord_2788772).sum := by decide
  have hdescent : baseEnd_2788772 < baseStart_2788772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788872 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_2788872 : Nat := 118140960795 + 2788872 * 2 ^ 59
def prefixEnd_2788872 : Nat := 4983230072969 + 3 ^ 40 * 2788872 * 2
def baseEnd_2788872 : Nat := 477343939955305919724739

theorem tailTrace_2788872 : CollatzResearch.WordTrace tailWord_2788872 prefixEnd_2788872 477343939955305919724739 := by
  unfold tailWord_2788872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50859259176200260131208435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67812345568267013508277913 50859259176200260131208435)
  ·
    refine ⟨76288888764300390196812653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50859259176200260131208435 76288888764300390196812653)
    ·
      refine ⟨28608333286612646323804745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76288888764300390196812653 28608333286612646323804745)
      ·
        refine ⟨21456249964959484742853559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28608333286612646323804745 21456249964959484742853559)
        ·
          refine ⟨32184374947439227114280339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21456249964959484742853559 32184374947439227114280339)
          ·
            refine ⟨48276562421158840671420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32184374947439227114280339 48276562421158840671420509)
            ·
              refine ⟨18103710907934565251782691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48276562421158840671420509 18103710907934565251782691)
              ·
                refine ⟨27155566361901847877674037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18103710907934565251782691 27155566361901847877674037)
                ·
                  refine ⟨2545834346428298238531941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27155566361901847877674037 2545834346428298238531941)
                  ·
                    refine ⟨477343939955305919724739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545834346428298238531941 477343939955305919724739)
                    ·
                      rfl

theorem cell23_2788872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_2788872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788872 prefixEnd_2788872 := by exact prefixLift 2788872
  have htrace : WordTrace (prefixWord ++ tailWord_2788872) baseStart_2788872 baseEnd_2788872 := by
    simpa [prefixWord, tailWord_2788872, baseEnd_2788872] using wordTrace_append hprefix tailTrace_2788872
  have hstable : (prefixWord ++ tailWord_2788872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788872).length < 2 ^ (prefixWord ++ tailWord_2788872).sum := by decide
  have hdescent : baseEnd_2788872 < baseStart_2788872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788876 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_2788876 : Nat := 118140960795 + 2788876 * 2 ^ 59
def prefixEnd_2788876 : Nat := 4983230072969 + 3 ^ 40 * 2788876 * 2
def baseEnd_2788876 : Nat := 477344624596178581174733

theorem tailTrace_2788876 : CollatzResearch.WordTrace tailWord_2788876 prefixEnd_2788876 477344624596178581174733 := by
  unfold tailWord_2788876
  simp only [CollatzResearch.WordTrace]
  refine ⟨50859332122193014472781241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67812442829590685963708321 50859332122193014472781241)
  ·
    refine ⟨38144499091644760854585931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50859332122193014472781241 38144499091644760854585931)
    ·
      refine ⟨57216748637467141281878897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38144499091644760854585931 57216748637467141281878897)
      ·
        refine ⟨42912561478100355961409173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57216748637467141281878897 42912561478100355961409173)
        ·
          refine ⟨2011526319285954185691055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42912561478100355961409173 2011526319285954185691055)
          ·
            refine ⟨3017289478928931278536583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011526319285954185691055 3017289478928931278536583)
            ·
              refine ⟨4525934218393396917804875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017289478928931278536583 4525934218393396917804875)
              ·
                refine ⟨6788901327590095376707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525934218393396917804875 6788901327590095376707313)
                ·
                  refine ⟨5091675995692571532530485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788901327590095376707313 5091675995692571532530485)
                  ·
                    refine ⟨477344624596178581174733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5091675995692571532530485 477344624596178581174733)
                    ·
                      rfl

theorem cell23_2788876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_2788876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788876 prefixEnd_2788876 := by exact prefixLift 2788876
  have htrace : WordTrace (prefixWord ++ tailWord_2788876) baseStart_2788876 baseEnd_2788876 := by
    simpa [prefixWord, tailWord_2788876, baseEnd_2788876] using wordTrace_append hprefix tailTrace_2788876
  have hstable : (prefixWord ++ tailWord_2788876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788876).length < 2 ^ (prefixWord ++ tailWord_2788876).sum := by decide
  have hdescent : baseEnd_2788876 < baseStart_2788876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788906 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2788906 : Nat := 118140960795 + 2788906 * 2 ^ 59
def prefixEnd_2788906 : Nat := 4983230072969 + 3 ^ 40 * 2788906 * 2
def baseEnd_2788906 : Nat := 477349759402723542049687

theorem tailTrace_2788906 : CollatzResearch.WordTrace tailWord_2788906 prefixEnd_2788906 477349759402723542049687 := by
  unfold tailWord_2788906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25429939608569336017288643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67813172289518229379436381 25429939608569336017288643)
  ·
    refine ⟨38144909412854004025932965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25429939608569336017288643 38144909412854004025932965)
    ·
      refine ⟨7152170514910125754862431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38144909412854004025932965 7152170514910125754862431)
      ·
        refine ⟨10728255772365188632293647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7152170514910125754862431 10728255772365188632293647)
        ·
          refine ⟨16092383658547782948440471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10728255772365188632293647 16092383658547782948440471)
          ·
            refine ⟨24138575487821674422660707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16092383658547782948440471 24138575487821674422660707)
            ·
              refine ⟨36207863231732511633991061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24138575487821674422660707 36207863231732511633991061)
              ·
                refine ⟨1697243588987461482843331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36207863231732511633991061 1697243588987461482843331)
                ·
                  refine ⟨2545865383481192224264997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697243588987461482843331 2545865383481192224264997)
                  ·
                    refine ⟨477349759402723542049687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545865383481192224264997 477349759402723542049687)
                    ·
                      rfl

theorem cell23_2788906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2788906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788906 prefixEnd_2788906 := by exact prefixLift 2788906
  have htrace : WordTrace (prefixWord ++ tailWord_2788906) baseStart_2788906 baseEnd_2788906 := by
    simpa [prefixWord, tailWord_2788906, baseEnd_2788906] using wordTrace_append hprefix tailTrace_2788906
  have hstable : (prefixWord ++ tailWord_2788906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788906).length < 2 ^ (prefixWord ++ tailWord_2788906).sum := by decide
  have hdescent : baseEnd_2788906 < baseStart_2788906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788919 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 6]
def baseStart_2788919 : Nat := 118140960795 + 2788919 * 2 ^ 59
def prefixEnd_2788919 : Nat := 4983230072969 + 3 ^ 40 * 2788919 * 2
def baseEnd_2788919 : Nat := 159117328161853230587389

theorem tailTrace_2788919 : CollatzResearch.WordTrace tailWord_2788919 prefixEnd_2788919 159117328161853230587389 := by
  unfold tailWord_2788919
  simp only [CollatzResearch.WordTrace]
  refine ⟨101720232583230247289377811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67813488388820164859585207 101720232583230247289377811)
  ·
    refine ⟨152580348874845370934066717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101720232583230247289377811 152580348874845370934066717)
    ·
      refine ⟨57217630828067014100275019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152580348874845370934066717 57217630828067014100275019)
      ·
        refine ⟨85826446242100521150412529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57217630828067014100275019 85826446242100521150412529)
        ·
          refine ⟨64369834681575390862809397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85826446242100521150412529 64369834681575390862809397)
          ·
            refine ⟨6034672001397692893388381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64369834681575390862809397 6034672001397692893388381)
            ·
              refine ⟨2263002000524134835020643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034672001397692893388381 2263002000524134835020643)
              ·
                refine ⟨3394503000786202252530965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263002000524134835020643 3394503000786202252530965)
                ·
                  refine ⟨159117328161853230587389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3394503000786202252530965 159117328161853230587389)
                  ·
                    rfl

theorem cell23_2788919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 6].length) (baseStart_2788919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788919 prefixEnd_2788919 := by exact prefixLift 2788919
  have htrace : WordTrace (prefixWord ++ tailWord_2788919) baseStart_2788919 baseEnd_2788919 := by
    simpa [prefixWord, tailWord_2788919, baseEnd_2788919] using wordTrace_append hprefix tailTrace_2788919
  have hstable : (prefixWord ++ tailWord_2788919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788919).length < 2 ^ (prefixWord ++ tailWord_2788919).sum := by decide
  have hdescent : baseEnd_2788919 < baseStart_2788919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788939 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 2, 3, 2]
def baseStart_2788939 : Nat := 118140960795 + 2788939 * 2 ^ 59
def prefixEnd_2788939 : Nat := 4983230072969 + 3 ^ 40 * 2788939 * 2
def baseEnd_2788939 : Nat := 1432066223069768997036409

theorem tailTrace_2788939 : CollatzResearch.WordTrace tailWord_2788939 prefixEnd_2788939 1432066223069768997036409 := by
  unfold tailWord_2788939
  simp only [CollatzResearch.WordTrace]
  refine ⟨101720962043157790705105871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67813974695438527136737247 101720962043157790705105871)
  ·
    refine ⟨152581443064736686057658807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101720962043157790705105871 152581443064736686057658807)
    ·
      refine ⟨228872164597105029086488211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152581443064736686057658807 228872164597105029086488211)
      ·
        refine ⟨343308246895657543629732317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228872164597105029086488211 343308246895657543629732317)
        ·
          refine ⟨128740592585871578861149619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343308246895657543629732317 128740592585871578861149619)
          ·
            refine ⟨193110888878807368291724429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128740592585871578861149619 193110888878807368291724429)
            ·
              refine ⟨72416583329552763109396661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193110888878807368291724429 72416583329552763109396661)
              ·
                refine ⟨6789054687145571541505937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72416583329552763109396661 6789054687145571541505937)
                ·
                  refine ⟨5091791015359178656129453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789054687145571541505937 5091791015359178656129453)
                  ·
                    refine ⟨1909421630759691996048545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091791015359178656129453 1909421630759691996048545)
                    ·
                      refine ⟨1432066223069768997036409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909421630759691996048545 1432066223069768997036409)
                      ·
                        rfl

theorem cell23_2788939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3, 2].length) (baseStart_2788939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788939 prefixEnd_2788939 := by exact prefixLift 2788939
  have htrace : WordTrace (prefixWord ++ tailWord_2788939) baseStart_2788939 baseEnd_2788939 := by
    simpa [prefixWord, tailWord_2788939, baseEnd_2788939] using wordTrace_append hprefix tailTrace_2788939
  have hstable : (prefixWord ++ tailWord_2788939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788939).length < 2 ^ (prefixWord ++ tailWord_2788939).sum := by decide
  have hdescent : baseEnd_2788939 < baseStart_2788939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788950 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2788950 : Nat := 118140960795 + 2788950 * 2 ^ 59
def prefixEnd_2788950 : Nat := 4983230072969 + 3 ^ 40 * 2788950 * 2
def baseEnd_2788950 : Nat := 1432071871356968453998859

theorem tailTrace_2788950 : CollatzResearch.WordTrace tailWord_2788950 prefixEnd_2788950 1432071871356968453998859 := by
  unfold tailWord_2788950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357585202882371223984769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67814242164078626389170869 6357585202882371223984769)
  ·
    refine ⟨4768188902161778417988577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6357585202882371223984769 4768188902161778417988577)
    ·
      refine ⟨3576141676621333813491433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4768188902161778417988577 3576141676621333813491433)
      ·
        refine ⟨2682106257466000360118575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3576141676621333813491433 2682106257466000360118575)
        ·
          refine ⟨4023159386199000540177863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682106257466000360118575 4023159386199000540177863)
          ·
            refine ⟨6034739079298500810266795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023159386199000540177863 6034739079298500810266795)
            ·
              refine ⟨9052108618947751215400193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034739079298500810266795 9052108618947751215400193)
              ·
                refine ⟨6789081464210813411550145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052108618947751215400193 6789081464210813411550145)
                ·
                  refine ⟨5091811098158110058662609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789081464210813411550145 5091811098158110058662609)
                  ·
                    refine ⟨3818858323618582543996957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091811098158110058662609 3818858323618582543996957)
                    ·
                      refine ⟨1432071871356968453998859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3818858323618582543996957 1432071871356968453998859)
                      ·
                        rfl

theorem cell23_2788950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2788950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788950 prefixEnd_2788950 := by exact prefixLift 2788950
  have htrace : WordTrace (prefixWord ++ tailWord_2788950) baseStart_2788950 baseEnd_2788950 := by
    simpa [prefixWord, tailWord_2788950, baseEnd_2788950] using wordTrace_append hprefix tailTrace_2788950
  have hstable : (prefixWord ++ tailWord_2788950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788950).length < 2 ^ (prefixWord ++ tailWord_2788950).sum := by decide
  have hdescent : baseEnd_2788950 < baseStart_2788950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788952 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2788952 : Nat := 118140960795 + 2788952 * 2 ^ 59
def prefixEnd_2788952 : Nat := 4983230072969 + 3 ^ 40 * 2788952 * 2
def baseEnd_2788952 : Nat := 1432072898318277446173849

theorem tailTrace_2788952 : CollatzResearch.WordTrace tailWord_2788952 prefixEnd_2788952 1432072898318277446173849 := by
  unfold tailWord_2788952
  simp only [CollatzResearch.WordTrace]
  refine ⟨50860718096055346962664555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67814290794740462616886073 50860718096055346962664555)
  ·
    refine ⟨76291077144083020443996833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50860718096055346962664555 76291077144083020443996833)
    ·
      refine ⟨57218307858062265332997625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76291077144083020443996833 57218307858062265332997625)
      ·
        refine ⟨42913730893546698999748219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57218307858062265332997625 42913730893546698999748219)
        ·
          refine ⟨64370596340320048499622329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42913730893546698999748219 64370596340320048499622329)
          ·
            refine ⟨48277947255240036374716747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64370596340320048499622329 48277947255240036374716747)
            ·
              refine ⟨72416920882860054562075121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48277947255240036374716747 72416920882860054562075121)
              ·
                refine ⟨54312690662145040921556341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72416920882860054562075121 54312690662145040921556341)
                ·
                  refine ⟨5091814749576097586395907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54312690662145040921556341 5091814749576097586395907)
                  ·
                    refine ⟨7637722124364146379593861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091814749576097586395907 7637722124364146379593861)
                    ·
                      refine ⟨1432072898318277446173849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7637722124364146379593861 1432072898318277446173849)
                      ·
                        rfl

theorem cell23_2788952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2788952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788952 prefixEnd_2788952 := by exact prefixLift 2788952
  have htrace : WordTrace (prefixWord ++ tailWord_2788952) baseStart_2788952 baseEnd_2788952 := by
    simpa [prefixWord, tailWord_2788952, baseEnd_2788952] using wordTrace_append hprefix tailTrace_2788952
  have hstable : (prefixWord ++ tailWord_2788952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788952).length < 2 ^ (prefixWord ++ tailWord_2788952).sum := by decide
  have hdescent : baseEnd_2788952 < baseStart_2788952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788956 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2788956 : Nat := 118140960795 + 2788956 * 2 ^ 59
def prefixEnd_2788956 : Nat := 4983230072969 + 3 ^ 40 * 2788956 * 2
def baseEnd_2788956 : Nat := 1432074952240895430523831

theorem tailTrace_2788956 : CollatzResearch.WordTrace tailWord_2788956 prefixEnd_2788956 1432074952240895430523831 := by
  unfold tailWord_2788956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50860791042048101304237361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67814388056064135072316481 50860791042048101304237361)
  ·
    refine ⟨38145593281536075978178021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50860791042048101304237361 38145593281536075978178021)
    ·
      refine ⟨7152298740288014245908379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38145593281536075978178021 7152298740288014245908379)
      ·
        refine ⟨10728448110432021368862569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7152298740288014245908379 10728448110432021368862569)
        ·
          refine ⟨8046336082824016026646927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10728448110432021368862569 8046336082824016026646927)
          ·
            refine ⟨12069504124236024039970391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046336082824016026646927 12069504124236024039970391)
            ·
              refine ⟨18104256186354036059955587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069504124236024039970391 18104256186354036059955587)
              ·
                refine ⟨27156384279531054089933381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18104256186354036059955587 27156384279531054089933381)
                ·
                  refine ⟨5091822052412072641862509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27156384279531054089933381 5091822052412072641862509)
                  ·
                    refine ⟨1909433269654527240698441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091822052412072641862509 1909433269654527240698441)
                    ·
                      refine ⟨1432074952240895430523831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909433269654527240698441 1432074952240895430523831)
                      ·
                        rfl

theorem cell23_2788956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2788956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788956 prefixEnd_2788956 := by exact prefixLift 2788956
  have htrace : WordTrace (prefixWord ++ tailWord_2788956) baseStart_2788956 baseEnd_2788956 := by
    simpa [prefixWord, tailWord_2788956, baseEnd_2788956] using wordTrace_append hprefix tailTrace_2788956
  have hstable : (prefixWord ++ tailWord_2788956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788956).length < 2 ^ (prefixWord ++ tailWord_2788956).sum := by decide
  have hdescent : baseEnd_2788956 < baseStart_2788956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788957 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2788957 : Nat := 118140960795 + 2788957 * 2 ^ 59
def prefixEnd_2788957 : Nat := 4983230072969 + 3 ^ 40 * 2788957 * 2
def baseEnd_2788957 : Nat := 477358488573849975537109

theorem tailTrace_2788957 : CollatzResearch.WordTrace tailWord_2788957 prefixEnd_2788957 477358488573849975537109 := by
  unfold tailWord_2788957
  simp only [CollatzResearch.WordTrace]
  refine ⟨101721618557092579779261125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67814412371395053186174083 101721618557092579779261125)
  ·
    refine ⟨19072803479454858708611461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101721618557092579779261125 19072803479454858708611461)
    ·
      refine ⟨3576150652397786007864649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19072803479454858708611461 3576150652397786007864649)
      ·
        refine ⟨2682112989298339505898487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3576150652397786007864649 2682112989298339505898487)
        ·
          refine ⟨4023169483947509258847731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682112989298339505898487 4023169483947509258847731)
          ·
            refine ⟨6034754225921263888271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023169483947509258847731 6034754225921263888271597)
            ·
              refine ⟨2263032834720473958101849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034754225921263888271597 2263032834720473958101849)
              ·
                refine ⟨1697274626040355468576387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263032834720473958101849 1697274626040355468576387)
                ·
                  refine ⟨2545911939060533202864581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697274626040355468576387 2545911939060533202864581)
                  ·
                    refine ⟨477358488573849975537109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545911939060533202864581 477358488573849975537109)
                    ·
                      rfl

theorem cell23_2788957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2788957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788957 prefixEnd_2788957 := by exact prefixLift 2788957
  have htrace : WordTrace (prefixWord ++ tailWord_2788957) baseStart_2788957 baseEnd_2788957 := by
    simpa [prefixWord, tailWord_2788957, baseEnd_2788957] using wordTrace_append hprefix tailTrace_2788957
  have hstable : (prefixWord ++ tailWord_2788957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788957).length < 2 ^ (prefixWord ++ tailWord_2788957).sum := by decide
  have hdescent : baseEnd_2788957 < baseStart_2788957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788972 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_2788972 : Nat := 118140960795 + 2788972 * 2 ^ 59
def prefixEnd_2788972 : Nat := 4983230072969 + 3 ^ 40 * 2788972 * 2
def baseEnd_2788972 : Nat := 1432083167931367367923757

theorem tailTrace_2788972 : CollatzResearch.WordTrace tailWord_2788972 prefixEnd_2788972 1432083167931367367923757 := by
  unfold tailWord_2788972
  simp only [CollatzResearch.WordTrace]
  refine ⟨50861082826019118670528585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67814777101358824894038113 50861082826019118670528585)
  ·
    refine ⟨38145812119514339002896439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50861082826019118670528585 38145812119514339002896439)
    ·
      refine ⟨57218718179271508504344659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38145812119514339002896439 57218718179271508504344659)
      ·
        refine ⟨85828077268907262756516989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57218718179271508504344659 85828077268907262756516989)
        ·
          refine ⟨32185528975840223533693871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85828077268907262756516989 32185528975840223533693871)
          ·
            refine ⟨48278293463760335300540807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32185528975840223533693871 48278293463760335300540807)
            ·
              refine ⟨72417440195640502950811211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48278293463760335300540807 72417440195640502950811211)
              ·
                refine ⟨108626160293460754426216817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72417440195640502950811211 108626160293460754426216817)
                ·
                  refine ⟨81469620220095565819662613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108626160293460754426216817 81469620220095565819662613)
                  ·
                    refine ⟨3818888447816979647796685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81469620220095565819662613 3818888447816979647796685)
                    ·
                      refine ⟨1432083167931367367923757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3818888447816979647796685 1432083167931367367923757)
                      ·
                        rfl

theorem cell23_2788972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_2788972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788972 prefixEnd_2788972 := by exact prefixLift 2788972
  have htrace : WordTrace (prefixWord ++ tailWord_2788972) baseStart_2788972 baseEnd_2788972 := by
    simpa [prefixWord, tailWord_2788972, baseEnd_2788972] using wordTrace_append hprefix tailTrace_2788972
  have hstable : (prefixWord ++ tailWord_2788972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788972).length < 2 ^ (prefixWord ++ tailWord_2788972).sum := by decide
  have hdescent : baseEnd_2788972 < baseStart_2788972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2788999 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2788999 : Nat := 118140960795 + 2788999 * 2 ^ 59
def prefixEnd_2788999 : Nat := 4983230072969 + 3 ^ 40 * 2788999 * 2
def baseEnd_2788999 : Nat := 1432097031909038762286133

theorem tailTrace_2788999 : CollatzResearch.WordTrace tailWord_2788999 prefixEnd_2788999 1432097031909038762286133 := by
  unfold tailWord_2788999
  simp only [CollatzResearch.WordTrace]
  refine ⟨101723150422940420952290051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67815433615293613968193367 101723150422940420952290051)
  ·
    refine ⟨152584725634410631428435077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101723150422940420952290051 152584725634410631428435077)
    ·
      refine ⟨28609636056451993392831577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152584725634410631428435077 28609636056451993392831577)
      ·
        refine ⟨21457227042338995044623683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28609636056451993392831577 21457227042338995044623683)
        ·
          refine ⟨32185840563508492566935525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21457227042338995044623683 32185840563508492566935525)
          ·
            refine ⟨6034845105657842356300411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32185840563508492566935525 6034845105657842356300411)
            ·
              refine ⟨9052267658486763534450617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034845105657842356300411 9052267658486763534450617)
              ·
                refine ⟨6789200743865072650837963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052267658486763534450617 6789200743865072650837963)
                ·
                  refine ⟨10183801115797608976256945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789200743865072650837963 10183801115797608976256945)
                  ·
                    refine ⟨7637850836848206732192709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10183801115797608976256945 7637850836848206732192709)
                    ·
                      refine ⟨1432097031909038762286133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7637850836848206732192709 1432097031909038762286133)
                      ·
                        rfl

theorem cell23_2788999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2788999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2788999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2788999 prefixEnd_2788999 := by exact prefixLift 2788999
  have htrace : WordTrace (prefixWord ++ tailWord_2788999) baseStart_2788999 baseEnd_2788999 := by
    simpa [prefixWord, tailWord_2788999, baseEnd_2788999] using wordTrace_append hprefix tailTrace_2788999
  have hstable : (prefixWord ++ tailWord_2788999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2788999).length < 2 ^ (prefixWord ++ tailWord_2788999).sum := by decide
  have hdescent : baseEnd_2788999 < baseStart_2788999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2788999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789003 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 1, 2, 2]
def baseStart_2789003 : Nat := 118140960795 + 2789003 * 2 ^ 59
def prefixEnd_2789003 : Nat := 4983230072969 + 3 ^ 40 * 2789003 * 2
def baseEnd_2789003 : Nat := 1432099085831656746636115

theorem tailTrace_2789003 : CollatzResearch.WordTrace tailWord_2789003 prefixEnd_2789003 1432099085831656746636115 := by
  unfold tailWord_2789003
  simp only [CollatzResearch.WordTrace]
  refine ⟨101723296314925929635435663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67815530876617286423623775 101723296314925929635435663)
  ·
    refine ⟨152584944472388894453153495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101723296314925929635435663 152584944472388894453153495)
    ·
      refine ⟨228877416708583341679730243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152584944472388894453153495 228877416708583341679730243)
      ·
        refine ⟨343316125062875012519595365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228877416708583341679730243 343316125062875012519595365)
        ·
          refine ⟨64371773449289064847424131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343316125062875012519595365 64371773449289064847424131)
          ·
            refine ⟨96557660173933597271136197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64371773449289064847424131 96557660173933597271136197)
            ·
              refine ⟨18104561282612549488338037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96557660173933597271136197 18104561282612549488338037)
              ·
                refine ⟨1697302620244926514531691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18104561282612549488338037 1697302620244926514531691)
                ·
                  refine ⟨2545953930367389771797537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697302620244926514531691 2545953930367389771797537)
                  ·
                    refine ⟨1909465447775542328848153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545953930367389771797537 1909465447775542328848153)
                    ·
                      refine ⟨1432099085831656746636115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909465447775542328848153 1432099085831656746636115)
                      ·
                        rfl

theorem cell23_2789003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 2, 2].length) (baseStart_2789003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789003 prefixEnd_2789003 := by exact prefixLift 2789003
  have htrace : WordTrace (prefixWord ++ tailWord_2789003) baseStart_2789003 baseEnd_2789003 := by
    simpa [prefixWord, tailWord_2789003, baseEnd_2789003] using wordTrace_append hprefix tailTrace_2789003
  have hstable : (prefixWord ++ tailWord_2789003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789003).length < 2 ^ (prefixWord ++ tailWord_2789003).sum := by decide
  have hdescent : baseEnd_2789003 < baseStart_2789003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789006 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2789006 : Nat := 118140960795 + 2789006 * 2 ^ 59
def prefixEnd_2789006 : Nat := 4983230072969 + 3 ^ 40 * 2789006 * 2
def baseEnd_2789006 : Nat := 1432100626273620234898601

theorem tailTrace_2789006 : CollatzResearch.WordTrace tailWord_2789006 prefixEnd_2789006 1432100626273620234898601 := by
  unfold tailWord_2789006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715425716739382643474359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67815603822610040765196581 12715425716739382643474359)
  ·
    refine ⟨19073138575109073965211539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12715425716739382643474359 19073138575109073965211539)
    ·
      refine ⟨28609707862663610947817309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19073138575109073965211539 28609707862663610947817309)
      ·
        refine ⟨10728640448498854105431491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28609707862663610947817309 10728640448498854105431491)
        ·
          refine ⟨16092960672748281158147237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10728640448498854105431491 16092960672748281158147237)
          ·
            refine ⟨3017430126140302717152607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16092960672748281158147237 3017430126140302717152607)
            ·
              refine ⟨4526145189210454075728911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017430126140302717152607 4526145189210454075728911)
              ·
                refine ⟨6789217783815681113593367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526145189210454075728911 6789217783815681113593367)
                ·
                  refine ⟨10183826675723521670390051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789217783815681113593367 10183826675723521670390051)
                  ·
                    refine ⟨15275740013585282505585077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10183826675723521670390051 15275740013585282505585077)
                    ·
                      refine ⟨1432100626273620234898601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15275740013585282505585077 1432100626273620234898601)
                      ·
                        rfl

theorem cell23_2789006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2789006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789006 prefixEnd_2789006 := by exact prefixLift 2789006
  have htrace : WordTrace (prefixWord ++ tailWord_2789006) baseStart_2789006 baseEnd_2789006 := by
    simpa [prefixWord, tailWord_2789006, baseEnd_2789006] using wordTrace_append hprefix tailTrace_2789006
  have hstable : (prefixWord ++ tailWord_2789006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789006).length < 2 ^ (prefixWord ++ tailWord_2789006).sum := by decide
  have hdescent : baseEnd_2789006 < baseStart_2789006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789193 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 1, 4]
def baseStart_2789193 : Nat := 118140960795 + 2789193 * 2 ^ 59
def prefixEnd_2789193 : Nat := 4983230072969 + 3 ^ 40 * 2789193 * 2
def baseEnd_2789193 : Nat := 477398882385337001086747

theorem tailTrace_2789193 : CollatzResearch.WordTrace tailWord_2789193 prefixEnd_2789193 477398882385337001086747 := by
  unfold tailWord_2789193
  simp only [CollatzResearch.WordTrace]
  refine ⟨101730226184237592084852233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67820150789491728056568155 101730226184237592084852233)
  ·
    refine ⟨76297669638178194063639175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101730226184237592084852233 76297669638178194063639175)
    ·
      refine ⟨114446504457267291095458763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76297669638178194063639175 114446504457267291095458763)
      ·
        refine ⟨171669756685900936643188145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114446504457267291095458763 171669756685900936643188145)
        ·
          refine ⟨128752317514425702482391109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171669756685900936643188145 128752317514425702482391109)
          ·
            refine ⟨24141059533954819215448333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128752317514425702482391109 24141059533954819215448333)
            ·
              refine ⟨9052897325233057205793125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24141059533954819215448333 9052897325233057205793125)
              ·
                refine ⟨1697418248481198226086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9052897325233057205793125 1697418248481198226086211)
                ·
                  refine ⟨2546127372721797339129317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697418248481198226086211 2546127372721797339129317)
                  ·
                    refine ⟨477398882385337001086747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546127372721797339129317 477398882385337001086747)
                    ·
                      rfl

theorem cell23_2789193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_2789193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789193 prefixEnd_2789193 := by exact prefixLift 2789193
  have htrace : WordTrace (prefixWord ++ tailWord_2789193) baseStart_2789193 baseEnd_2789193 := by
    simpa [prefixWord, tailWord_2789193, baseEnd_2789193] using wordTrace_append hprefix tailTrace_2789193
  have hstable : (prefixWord ++ tailWord_2789193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789193).length < 2 ^ (prefixWord ++ tailWord_2789193).sum := by decide
  have hdescent : baseEnd_2789193 < baseStart_2789193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789220 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_2789220 : Nat := 118140960795 + 2789220 * 2 ^ 59
def prefixEnd_2789220 : Nat := 4983230072969 + 3 ^ 40 * 2789220 * 2
def baseEnd_2789220 : Nat := 1432210511133682397622617

theorem tailTrace_2789220 : CollatzResearch.WordTrace tailWord_2789220 prefixEnd_2789220 1432210511133682397622617 := by
  unfold tailWord_2789220
  simp only [CollatzResearch.WordTrace]
  refine ⟨50865605477569887848042557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67820807303426517130723409 50865605477569887848042557)
  ·
    refine ⟨19074602054088707943015959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50865605477569887848042557 19074602054088707943015959)
    ·
      refine ⟨28611903081133061914523939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19074602054088707943015959 28611903081133061914523939)
      ·
        refine ⟨42917854621699592871785909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611903081133061914523939 42917854621699592871785909)
        ·
          refine ⟨4023548870784336831729929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42917854621699592871785909 4023548870784336831729929)
          ·
            refine ⟨3017661653088252623797447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023548870784336831729929 3017661653088252623797447)
            ·
              refine ⟨4526492479632378935696171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017661653088252623797447 4526492479632378935696171)
              ·
                refine ⟨6789738719448568403544257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526492479632378935696171 6789738719448568403544257)
                ·
                  refine ⟨5092304039586426302658193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789738719448568403544257 5092304039586426302658193)
                  ·
                    refine ⟨3819228029689819726993645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5092304039586426302658193 3819228029689819726993645)
                    ·
                      refine ⟨1432210511133682397622617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3819228029689819726993645 1432210511133682397622617)
                      ·
                        rfl

theorem cell23_2789220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_2789220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789220 prefixEnd_2789220 := by exact prefixLift 2789220
  have htrace : WordTrace (prefixWord ++ tailWord_2789220) baseStart_2789220 baseEnd_2789220 := by
    simpa [prefixWord, tailWord_2789220, baseEnd_2789220] using wordTrace_append hprefix tailTrace_2789220
  have hstable : (prefixWord ++ tailWord_2789220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789220).length < 2 ^ (prefixWord ++ tailWord_2789220).sum := by decide
  have hdescent : baseEnd_2789220 < baseStart_2789220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789306 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_2789306 : Nat := 118140960795 + 2789306 * 2 ^ 59
def prefixEnd_2789306 : Nat := 4983230072969 + 3 ^ 40 * 2789306 * 2
def baseEnd_2789306 : Nat := 1432254670469969061147221

theorem tailTrace_2789306 : CollatzResearch.WordTrace tailWord_2789306 prefixEnd_2789306 1432254670469969061147221 := by
  unfold tailWord_2789306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25433586908207053095928943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67822898421885474922477181 25433586908207053095928943)
  ·
    refine ⟨38150380362310579643893415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25433586908207053095928943 38150380362310579643893415)
    ·
      refine ⟨57225570543465869465840123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38150380362310579643893415 57225570543465869465840123)
      ·
        refine ⟨85838355815198804198760185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57225570543465869465840123 85838355815198804198760185)
        ·
          refine ⟨64378766861399103149070139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85838355815198804198760185 64378766861399103149070139)
          ·
            refine ⟨96568150292098654723605209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64378766861399103149070139 96568150292098654723605209)
            ·
              refine ⟨72426112719073991042703907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96568150292098654723605209 72426112719073991042703907)
              ·
                refine ⟨108639169078610986564055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72426112719073991042703907 108639169078610986564055861)
                ·
                  refine ⟨10184922101119779990380237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108639169078610986564055861 10184922101119779990380237)
                  ·
                    refine ⟨3819345787919917496392589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10184922101119779990380237 3819345787919917496392589)
                    ·
                      refine ⟨1432254670469969061147221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3819345787919917496392589 1432254670469969061147221)
                      ·
                        rfl

theorem cell23_2789306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_2789306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789306 prefixEnd_2789306 := by exact prefixLift 2789306
  have htrace : WordTrace (prefixWord ++ tailWord_2789306) baseStart_2789306 baseEnd_2789306 := by
    simpa [prefixWord, tailWord_2789306, baseEnd_2789306] using wordTrace_append hprefix tailTrace_2789306
  have hstable : (prefixWord ++ tailWord_2789306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789306).length < 2 ^ (prefixWord ++ tailWord_2789306).sum := by decide
  have hdescent : baseEnd_2789306 < baseStart_2789306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789413 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_2789413 : Nat := 118140960795 + 2789413 * 2 ^ 59
def prefixEnd_2789413 : Nat := 4983230072969 + 3 ^ 40 * 2789413 * 2
def baseEnd_2789413 : Nat := 1432309612900000142509229

theorem tailTrace_2789413 : CollatzResearch.WordTrace tailWord_2789413 prefixEnd_2789413 1432309612900000142509229 := by
  unfold tailWord_2789413
  simp only [CollatzResearch.WordTrace]
  refine ⟨101738250243440569657860893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67825500162293713105240595 101738250243440569657860893)
  ·
    refine ⟨38151843841290213621697835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101738250243440569657860893 38151843841290213621697835)
    ·
      refine ⟨57227765761935320432546753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38151843841290213621697835 57227765761935320432546753)
      ·
        refine ⟨42920824321451490324410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57227765761935320432546753 42920824321451490324410065)
        ·
          refine ⟨32190618241088617743307549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42920824321451490324410065 32190618241088617743307549)
          ·
            refine ⟨12071481840408231653740331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32190618241088617743307549 12071481840408231653740331)
            ·
              refine ⟨18107222760612347480610497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12071481840408231653740331 18107222760612347480610497)
              ·
                refine ⟨13580417070459260610457873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18107222760612347480610497 13580417070459260610457873)
                ·
                  refine ⟨10185312802844445457843405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13580417070459260610457873 10185312802844445457843405)
                  ·
                    refine ⟨3819492301066667046691277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10185312802844445457843405 3819492301066667046691277)
                    ·
                      refine ⟨1432309612900000142509229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3819492301066667046691277 1432309612900000142509229)
                      ·
                        rfl

theorem cell23_2789413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_2789413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789413 prefixEnd_2789413 := by exact prefixLift 2789413
  have htrace : WordTrace (prefixWord ++ tailWord_2789413) baseStart_2789413 baseEnd_2789413 := by
    simpa [prefixWord, tailWord_2789413, baseEnd_2789413] using wordTrace_append hprefix tailTrace_2789413
  have hstable : (prefixWord ++ tailWord_2789413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789413).length < 2 ^ (prefixWord ++ tailWord_2789413).sum := by decide
  have hdescent : baseEnd_2789413 < baseStart_2789413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789423 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 5, 2]
def baseStart_2789423 : Nat := 118140960795 + 2789423 * 2 ^ 59
def prefixEnd_2789423 : Nat := 4983230072969 + 3 ^ 40 * 2789423 * 2
def baseEnd_2789423 : Nat := 1432314747706545103384183

theorem tailTrace_2789423 : CollatzResearch.WordTrace tailWord_2789423 prefixEnd_2789423 1432314747706545103384183 := by
  unfold tailWord_2789423
  simp only [CollatzResearch.WordTrace]
  refine ⟨101738614973404341365724923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67825743315602894243816615 101738614973404341365724923)
  ·
    refine ⟨152607922460106512048587385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101738614973404341365724923 152607922460106512048587385)
    ·
      refine ⟨114455941845079884036440539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152607922460106512048587385 114455941845079884036440539)
      ·
        refine ⟨171683912767619826054660809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114455941845079884036440539 171683912767619826054660809)
        ·
          refine ⟨128762934575714869540995607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171683912767619826054660809 128762934575714869540995607)
          ·
            refine ⟨193144401863572304311493411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128762934575714869540995607 193144401863572304311493411)
            ·
              refine ⟨289716602795358456467240117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193144401863572304311493411 289716602795358456467240117)
              ·
                refine ⟨27160931512064855293803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 289716602795358456467240117 27160931512064855293803761)
                ·
                  refine ⟨20370698634048641470352821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27160931512064855293803761 20370698634048641470352821)
                  ·
                    refine ⟨1909752996942060137845577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20370698634048641470352821 1909752996942060137845577)
                    ·
                      refine ⟨1432314747706545103384183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909752996942060137845577 1432314747706545103384183)
                      ·
                        rfl

theorem cell23_2789423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 5, 2].length) (baseStart_2789423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789423 prefixEnd_2789423 := by exact prefixLift 2789423
  have htrace : WordTrace (prefixWord ++ tailWord_2789423) baseStart_2789423 baseEnd_2789423 := by
    simpa [prefixWord, tailWord_2789423, baseEnd_2789423] using wordTrace_append hprefix tailTrace_2789423
  have hstable : (prefixWord ++ tailWord_2789423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789423).length < 2 ^ (prefixWord ++ tailWord_2789423).sum := by decide
  have hdescent : baseEnd_2789423 < baseStart_2789423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789430 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2789430 : Nat := 118140960795 + 2789430 * 2 ^ 59
def prefixEnd_2789430 : Nat := 4983230072969 + 3 ^ 40 * 2789430 * 2
def baseEnd_2789430 : Nat := 1432318342071126575996651

theorem tailTrace_2789430 : CollatzResearch.WordTrace tailWord_2789430 prefixEnd_2789430 1432318342071126575996651 := by
  unfold tailWord_2789430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358679392773686347576859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67825913522919321040819829 6358679392773686347576859)
  ·
    refine ⟨9538019089160529521365289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6358679392773686347576859 9538019089160529521365289)
    ·
      refine ⟨7153514316870397141023967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9538019089160529521365289 7153514316870397141023967)
      ·
        refine ⟨10730271475305595711535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7153514316870397141023967 10730271475305595711535951)
        ·
          refine ⟨16095407212958393567303927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10730271475305595711535951 16095407212958393567303927)
          ·
            refine ⟨24143110819437590350955891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16095407212958393567303927 24143110819437590350955891)
            ·
              refine ⟨36214666229156385526433837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24143110819437590350955891 36214666229156385526433837)
              ·
                refine ⟨13580499835933644572412689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36214666229156385526433837 13580499835933644572412689)
                ·
                  refine ⟨10185374876950233429309517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13580499835933644572412689 10185374876950233429309517)
                  ·
                    refine ⟨3819515578856337535991069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10185374876950233429309517 3819515578856337535991069)
                    ·
                      refine ⟨1432318342071126575996651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3819515578856337535991069 1432318342071126575996651)
                      ·
                        rfl

theorem cell23_2789430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2789430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789430 prefixEnd_2789430 := by exact prefixLift 2789430
  have htrace : WordTrace (prefixWord ++ tailWord_2789430) baseStart_2789430 baseEnd_2789430 := by
    simpa [prefixWord, tailWord_2789430, baseEnd_2789430] using wordTrace_append hprefix tailTrace_2789430
  have hstable : (prefixWord ++ tailWord_2789430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789430).length < 2 ^ (prefixWord ++ tailWord_2789430).sum := by decide
  have hdescent : baseEnd_2789430 < baseStart_2789430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789456 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_2789456 : Nat := 118140960795 + 2789456 * 2 ^ 59
def prefixEnd_2789456 : Nat := 4983230072969 + 3 ^ 40 * 2789456 * 2
def baseEnd_2789456 : Nat := 1432331692568143474271531

theorem tailTrace_2789456 : CollatzResearch.WordTrace tailWord_2789456 prefixEnd_2789456 1432331692568143474271531 := by
  unfold tailWord_2789456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50869909291142394000838111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67826545721523192001117481 50869909291142394000838111)
  ·
    refine ⟨76304863936713591001257167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50869909291142394000838111 76304863936713591001257167)
    ·
      refine ⟨114457295905070386501885751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76304863936713591001257167 114457295905070386501885751)
      ·
        refine ⟨171685943857605579752828627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114457295905070386501885751 171685943857605579752828627)
        ·
          refine ⟨257528915786408369629242941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171685943857605579752828627 257528915786408369629242941)
          ·
            refine ⟨96573343419903138610966103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257528915786408369629242941 96573343419903138610966103)
            ·
              refine ⟨144860015129854707916449155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96573343419903138610966103 144860015129854707916449155)
              ·
                refine ⟨217290022694782061874673733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144860015129854707916449155 217290022694782061874673733)
                ·
                  refine ⟨40741879255271636601501325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217290022694782061874673733 40741879255271636601501325)
                  ·
                    refine ⟨15278204720726863725562997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40741879255271636601501325 15278204720726863725562997)
                    ·
                      refine ⟨1432331692568143474271531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15278204720726863725562997 1432331692568143474271531)
                      ·
                        rfl

theorem cell23_2789456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_2789456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789456 prefixEnd_2789456 := by exact prefixLift 2789456
  have htrace : WordTrace (prefixWord ++ tailWord_2789456) baseStart_2789456 baseEnd_2789456 := by
    simpa [prefixWord, tailWord_2789456, baseEnd_2789456] using wordTrace_append hprefix tailTrace_2789456
  have hstable : (prefixWord ++ tailWord_2789456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789456).length < 2 ^ (prefixWord ++ tailWord_2789456).sum := by decide
  have hdescent : baseEnd_2789456 < baseStart_2789456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789463 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 5, 4]
def baseStart_2789463 : Nat := 118140960795 + 2789463 * 2 ^ 59
def prefixEnd_2789463 : Nat := 4983230072969 + 3 ^ 40 * 2789463 * 2
def baseEnd_2789463 : Nat := 477445095644241648961333

theorem tailTrace_2789463 : CollatzResearch.WordTrace tailWord_2789463 prefixEnd_2789463 477445095644241648961333 := by
  unfold tailWord_2789463
  simp only [CollatzResearch.WordTrace]
  refine ⟨101740073893259428197181043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67826715928839618798120695 101740073893259428197181043)
  ·
    refine ⟨152610110839889142295771565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101740073893259428197181043 152610110839889142295771565)
    ·
      refine ⟨57228791564958428360914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152610110839889142295771565 57228791564958428360914337)
      ·
        refine ⟨42921593673718821270685753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57228791564958428360914337 42921593673718821270685753)
        ·
          refine ⟨32191195255289115953014315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42921593673718821270685753 32191195255289115953014315)
          ·
            refine ⟨48286792882933673929521473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32191195255289115953014315 48286792882933673929521473)
            ·
              refine ⟨36215094662200255447141105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48286792882933673929521473 36215094662200255447141105)
              ·
                refine ⟨27161320996650191585355829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36215094662200255447141105 27161320996650191585355829)
                ·
                  refine ⟨2546373843435955461127109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27161320996650191585355829 2546373843435955461127109)
                  ·
                    refine ⟨477445095644241648961333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546373843435955461127109 477445095644241648961333)
                    ·
                      rfl

theorem cell23_2789463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_2789463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789463 prefixEnd_2789463 := by exact prefixLift 2789463
  have htrace : WordTrace (prefixWord ++ tailWord_2789463) baseStart_2789463 baseEnd_2789463 := by
    simpa [prefixWord, tailWord_2789463, baseEnd_2789463] using wordTrace_append hprefix tailTrace_2789463
  have hstable : (prefixWord ++ tailWord_2789463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789463).length < 2 ^ (prefixWord ++ tailWord_2789463).sum := by decide
  have hdescent : baseEnd_2789463 < baseStart_2789463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789560 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_2789560 : Nat := 118140960795 + 2789560 * 2 ^ 59
def prefixEnd_2789560 : Nat := 4983230072969 + 3 ^ 40 * 2789560 * 2
def baseEnd_2789560 : Nat := 1432385094556211067371053

theorem tailTrace_2789560 : CollatzResearch.WordTrace tailWord_2789560 prefixEnd_2789560 1432385094556211067371053 := by
  unfold tailWord_2789560
  simp only [CollatzResearch.WordTrace]
  refine ⟨50871805886954006881731067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67829074515938675842308089 50871805886954006881731067)
  ·
    refine ⟨76307708830431010322596601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50871805886954006881731067 76307708830431010322596601)
    ·
      refine ⟨57230781622823257741947451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76307708830431010322596601 57230781622823257741947451)
      ·
        refine ⟨85846172434234886612921177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57230781622823257741947451 85846172434234886612921177)
        ·
          refine ⟨64384629325676164959690883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85846172434234886612921177 64384629325676164959690883)
          ·
            refine ⟨96576943988514247439536325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64384629325676164959690883 96576943988514247439536325)
            ·
              refine ⟨18108176997846421394913061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96576943988514247439536325 18108176997846421394913061)
              ·
                refine ⟨3395283187096204011546199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18108176997846421394913061 3395283187096204011546199)
                ·
                  refine ⟨5092924780644306017319299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395283187096204011546199 5092924780644306017319299)
                  ·
                    refine ⟨7639387170966459025978949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5092924780644306017319299 7639387170966459025978949)
                    ·
                      refine ⟨1432385094556211067371053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7639387170966459025978949 1432385094556211067371053)
                      ·
                        rfl

theorem cell23_2789560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_2789560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789560 prefixEnd_2789560 := by exact prefixLift 2789560
  have htrace : WordTrace (prefixWord ++ tailWord_2789560) baseStart_2789560 baseEnd_2789560 := by
    simpa [prefixWord, tailWord_2789560, baseEnd_2789560] using wordTrace_append hprefix tailTrace_2789560
  have hstable : (prefixWord ++ tailWord_2789560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789560).length < 2 ^ (prefixWord ++ tailWord_2789560).sum := by decide
  have hdescent : baseEnd_2789560 < baseStart_2789560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789597 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2789597 : Nat := 118140960795 + 2789597 * 2 ^ 59
def prefixEnd_2789597 : Nat := 4983230072969 + 3 ^ 40 * 2789597 * 2
def baseEnd_2789597 : Nat := 1432404093340427422608383

theorem tailTrace_2789597 : CollatzResearch.WordTrace tailWord_2789597 prefixEnd_2789597 1432404093340427422608383 := by
  unfold tailWord_2789597
  simp only [CollatzResearch.WordTrace]
  refine ⟨101744961274773969082559045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67829974183182646055039363 101744961274773969082559045)
  ·
    refine ⟨19077180239020119202979821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101744961274773969082559045 19077180239020119202979821)
    ·
      refine ⟨7153942589632544701117433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19077180239020119202979821 7153942589632544701117433)
      ·
        refine ⟨5365456942224408525838075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153942589632544701117433 5365456942224408525838075)
        ·
          refine ⟨8048185413336612788757113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365456942224408525838075 8048185413336612788757113)
          ·
            refine ⟨6036139060002459591567835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8048185413336612788757113 6036139060002459591567835)
            ·
              refine ⟨9054208590003689387351753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036139060002459591567835 9054208590003689387351753)
              ·
                refine ⟨6790656442502767040513815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9054208590003689387351753 6790656442502767040513815)
                ·
                  refine ⟨10185984663754150560770723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790656442502767040513815 10185984663754150560770723)
                  ·
                    refine ⟨15278976995631225841156085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10185984663754150560770723 15278976995631225841156085)
                    ·
                      refine ⟨1432404093340427422608383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15278976995631225841156085 1432404093340427422608383)
                      ·
                        rfl

theorem cell23_2789597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2789597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789597 prefixEnd_2789597 := by exact prefixLift 2789597
  have htrace : WordTrace (prefixWord ++ tailWord_2789597) baseStart_2789597 baseEnd_2789597 := by
    simpa [prefixWord, tailWord_2789597, baseEnd_2789597] using wordTrace_append hprefix tailTrace_2789597
  have hstable : (prefixWord ++ tailWord_2789597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789597).length < 2 ^ (prefixWord ++ tailWord_2789597).sum := by decide
  have hdescent : baseEnd_2789597 < baseStart_2789597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789607 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2789607 : Nat := 118140960795 + 2789607 * 2 ^ 59
def prefixEnd_2789607 : Nat := 4983230072969 + 3 ^ 40 * 2789607 * 2
def baseEnd_2789607 : Nat := 1432409228146972383483337

theorem tailTrace_2789607 : CollatzResearch.WordTrace tailWord_2789607 prefixEnd_2789607 1432409228146972383483337 := by
  unfold tailWord_2789607
  simp only [CollatzResearch.WordTrace]
  refine ⟨101745326004737740790423075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67830217336491827193615383 101745326004737740790423075)
  ·
    refine ⟨152617989007106611185634613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101745326004737740790423075 152617989007106611185634613)
    ·
      refine ⟨14307936469416244798653245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152617989007106611185634613 14307936469416244798653245)
      ·
        refine ⟨5365476176031091799494967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14307936469416244798653245 5365476176031091799494967)
        ·
          refine ⟨8048214264046637699242451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365476176031091799494967 8048214264046637699242451)
          ·
            refine ⟨12072321396069956548863677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048214264046637699242451 12072321396069956548863677)
            ·
              refine ⟨4527120523526233705823879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12072321396069956548863677 4527120523526233705823879)
              ·
                refine ⟨6790680785289350558735819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527120523526233705823879 6790680785289350558735819)
                ·
                  refine ⟨10186021177934025838103729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790680785289350558735819 10186021177934025838103729)
                  ·
                    refine ⟨7639515883450519378577797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10186021177934025838103729 7639515883450519378577797)
                    ·
                      refine ⟨1432409228146972383483337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7639515883450519378577797 1432409228146972383483337)
                      ·
                        rfl

theorem cell23_2789607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2789607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789607 prefixEnd_2789607 := by exact prefixLift 2789607
  have htrace : WordTrace (prefixWord ++ tailWord_2789607) baseStart_2789607 baseEnd_2789607 := by
    simpa [prefixWord, tailWord_2789607, baseEnd_2789607] using wordTrace_append hprefix tailTrace_2789607
  have hstable : (prefixWord ++ tailWord_2789607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789607).length < 2 ^ (prefixWord ++ tailWord_2789607).sum := by decide
  have hdescent : baseEnd_2789607 < baseStart_2789607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789628 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_2789628 : Nat := 118140960795 + 2789628 * 2 ^ 59
def prefixEnd_2789628 : Nat := 4983230072969 + 3 ^ 40 * 2789628 * 2
def baseEnd_2789628 : Nat := 1432420011240716801320741

theorem tailTrace_2789628 : CollatzResearch.WordTrace tailWord_2789628 prefixEnd_2789628 1432420011240716801320741 := by
  unfold tailWord_2789628
  simp only [CollatzResearch.WordTrace]
  refine ⟨50873045968830830688468769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67830727958441107584625025 50873045968830830688468769)
  ·
    refine ⟨38154784476623123016351577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50873045968830830688468769 38154784476623123016351577)
    ·
      refine ⟨28616088357467342262263683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38154784476623123016351577 28616088357467342262263683)
      ·
        refine ⟨42924132536201013393395525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616088357467342262263683 42924132536201013393395525)
        ·
          refine ⟨8048274850537690011261661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42924132536201013393395525 8048274850537690011261661)
          ·
            refine ⟨3018103068951633754223123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8048274850537690011261661 3018103068951633754223123)
            ·
              refine ⟨4527154603427450631334685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018103068951633754223123 4527154603427450631334685)
              ·
                refine ⟨1697682976285293986750507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4527154603427450631334685 1697682976285293986750507)
                ·
                  refine ⟨2546524464427940980125761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697682976285293986750507 2546524464427940980125761)
                  ·
                    refine ⟨1909893348320955735094321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2546524464427940980125761 1909893348320955735094321)
                    ·
                      refine ⟨1432420011240716801320741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909893348320955735094321 1432420011240716801320741)
                      ·
                        rfl

theorem cell23_2789628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_2789628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789628 prefixEnd_2789628 := by exact prefixLift 2789628
  have htrace : WordTrace (prefixWord ++ tailWord_2789628) baseStart_2789628 baseEnd_2789628 := by
    simpa [prefixWord, tailWord_2789628, baseEnd_2789628] using wordTrace_append hprefix tailTrace_2789628
  have hstable : (prefixWord ++ tailWord_2789628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789628).length < 2 ^ (prefixWord ++ tailWord_2789628).sum := by decide
  have hdescent : baseEnd_2789628 < baseStart_2789628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789661 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2789661 : Nat := 118140960795 + 2789661 * 2 ^ 59
def prefixEnd_2789661 : Nat := 4983230072969 + 3 ^ 40 * 2789661 * 2
def baseEnd_2789661 : Nat := 1432436956102315172208089

theorem tailTrace_2789661 : CollatzResearch.WordTrace tailWord_2789661 prefixEnd_2789661 1432436956102315172208089 := by
  unfold tailWord_2789661
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747295546542108012888837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67831530364361405341925891 101747295546542108012888837)
  ·
    refine ⟨19077617914976645252416657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101747295546542108012888837 19077617914976645252416657)
    ·
      refine ⟨14308213436232483939312493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19077617914976645252416657 14308213436232483939312493)
      ·
        refine ⟨5365580038587181477242185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14308213436232483939312493 5365580038587181477242185)
        ·
          refine ⟨4024185028940386107931639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5365580038587181477242185 4024185028940386107931639)
          ·
            refine ⟨6036277543410579161897459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024185028940386107931639 6036277543410579161897459)
            ·
              refine ⟨9054416315115868742846189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036277543410579161897459 9054416315115868742846189)
              ·
                refine ⟨3395406118168450778567321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9054416315115868742846189 3395406118168450778567321)
                ·
                  refine ⟨2546554588626338083925491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395406118168450778567321 2546554588626338083925491)
                  ·
                    refine ⟨3819831882939507125888237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546554588626338083925491 3819831882939507125888237)
                    ·
                      refine ⟨1432436956102315172208089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3819831882939507125888237 1432436956102315172208089)
                      ·
                        rfl

theorem cell23_2789661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2789661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789661 prefixEnd_2789661 := by exact prefixLift 2789661
  have htrace : WordTrace (prefixWord ++ tailWord_2789661) baseStart_2789661 baseEnd_2789661 := by
    simpa [prefixWord, tailWord_2789661, baseEnd_2789661] using wordTrace_append hprefix tailTrace_2789661
  have hstable : (prefixWord ++ tailWord_2789661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789661).length < 2 ^ (prefixWord ++ tailWord_2789661).sum := by decide
  have hdescent : baseEnd_2789661 < baseStart_2789661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789667 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 4, 2]
def baseStart_2789667 : Nat := 118140960795 + 2789667 * 2 ^ 59
def prefixEnd_2789667 : Nat := 4983230072969 + 3 ^ 40 * 2789667 * 2
def baseEnd_2789667 : Nat := 1432440036986242148733061

theorem tailTrace_2789667 : CollatzResearch.WordTrace tailWord_2789667 prefixEnd_2789667 1432440036986242148733061 := by
  unfold tailWord_2789667
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747514384520371037607255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67831676256346914025071503 101747514384520371037607255)
  ·
    refine ⟨152621271576780556556410883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101747514384520371037607255 152621271576780556556410883)
    ·
      refine ⟨228931907365170834834616325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152621271576780556556410883 228931907365170834834616325)
      ·
        refine ⟨42924732630969531531490561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228931907365170834834616325 42924732630969531531490561)
        ·
          refine ⟨32193549473227148648617921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42924732630969531531490561 32193549473227148648617921)
          ·
            refine ⟨24145162104920361486463441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32193549473227148648617921 24145162104920361486463441)
            ·
              refine ⟨18108871578690271114847581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24145162104920361486463441 18108871578690271114847581)
              ·
                refine ⟨6790826842008851668067843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18108871578690271114847581 6790826842008851668067843)
                ·
                  refine ⟨10186240263013277502101765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790826842008851668067843 10186240263013277502101765)
                  ·
                    refine ⟨1909920049314989531644081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10186240263013277502101765 1909920049314989531644081)
                    ·
                      refine ⟨1432440036986242148733061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909920049314989531644081 1432440036986242148733061)
                      ·
                        rfl

theorem cell23_2789667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_2789667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789667 prefixEnd_2789667 := by exact prefixLift 2789667
  have htrace : WordTrace (prefixWord ++ tailWord_2789667) baseStart_2789667 baseEnd_2789667 := by
    simpa [prefixWord, tailWord_2789667, baseEnd_2789667] using wordTrace_append hprefix tailTrace_2789667
  have hstable : (prefixWord ++ tailWord_2789667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789667).length < 2 ^ (prefixWord ++ tailWord_2789667).sum := by decide
  have hdescent : baseEnd_2789667 < baseStart_2789667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789684 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_2789684 : Nat := 118140960795 + 2789684 * 2 ^ 59
def prefixEnd_2789684 : Nat := 4983230072969 + 3 ^ 40 * 2789684 * 2
def baseEnd_2789684 : Nat := 1432448766157368582220483

theorem tailTrace_2789684 : CollatzResearch.WordTrace tailWord_2789684 prefixEnd_2789684 1432448766157368582220483 := by
  unfold tailWord_2789684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874067212729391470488053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67832089616972521960650737 50874067212729391470488053)
  ·
    refine ⟨4769443801193380450358255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50874067212729391470488053 4769443801193380450358255)
    ·
      refine ⟨7154165701790070675537383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769443801193380450358255 7154165701790070675537383)
      ·
        refine ⟨10731248552685106013306075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7154165701790070675537383 10731248552685106013306075)
        ·
          refine ⟨16096872829027659019959113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10731248552685106013306075 16096872829027659019959113)
          ·
            refine ⟨12072654621770744264969335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16096872829027659019959113 12072654621770744264969335)
            ·
              refine ⟨18108981932656116397454003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12072654621770744264969335 18108981932656116397454003)
              ·
                refine ⟨27163472898984174596181005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18108981932656116397454003 27163472898984174596181005)
                ·
                  refine ⟨10186302337119065473567877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27163472898984174596181005 10186302337119065473567877)
                  ·
                    refine ⟨1909931688209824776293977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10186302337119065473567877 1909931688209824776293977)
                    ·
                      refine ⟨1432448766157368582220483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1909931688209824776293977 1432448766157368582220483)
                      ·
                        rfl

theorem cell23_2789684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_2789684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789684 prefixEnd_2789684 := by exact prefixLift 2789684
  have htrace : WordTrace (prefixWord ++ tailWord_2789684) baseStart_2789684 baseEnd_2789684 := by
    simpa [prefixWord, tailWord_2789684, baseEnd_2789684] using wordTrace_append hprefix tailTrace_2789684
  have hstable : (prefixWord ++ tailWord_2789684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789684).length < 2 ^ (prefixWord ++ tailWord_2789684).sum := by decide
  have hdescent : baseEnd_2789684 < baseStart_2789684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789724 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 7]
def baseStart_2789724 : Nat := 118140960795 + 2789724 * 2 ^ 59
def prefixEnd_2789724 : Nat := 4983230072969 + 3 ^ 40 * 2789724 * 2
def baseEnd_2789724 : Nat := 159163256153727602857811

theorem tailTrace_2789724 : CollatzResearch.WordTrace tailWord_2789724 prefixEnd_2789724 159163256153727602857811 := by
  unfold tailWord_2789724
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874796672656934886216113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67833062230209246514954817 50874796672656934886216113)
  ·
    refine ⟨38156097504492701164662085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50874796672656934886216113 38156097504492701164662085)
    ·
      refine ⟨7154268282092381468374141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38156097504492701164662085 7154268282092381468374141)
      ·
        refine ⟨2682850605784643050640303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7154268282092381468374141 2682850605784643050640303)
        ·
          refine ⟨4024275908676964575960455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682850605784643050640303 4024275908676964575960455)
          ·
            refine ⟨6036413863015446863940683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024275908676964575960455 6036413863015446863940683)
            ·
              refine ⟨9054620794523170295911025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036413863015446863940683 9054620794523170295911025)
              ·
                refine ⟨6790965595892377721933269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9054620794523170295911025 6790965595892377721933269)
                ·
                  refine ⟨159163256153727602857811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6790965595892377721933269 159163256153727602857811)
                  ·
                    rfl

theorem cell23_2789724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_2789724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789724 prefixEnd_2789724 := by exact prefixLift 2789724
  have htrace : WordTrace (prefixWord ++ tailWord_2789724) baseStart_2789724 baseEnd_2789724 := by
    simpa [prefixWord, tailWord_2789724, baseEnd_2789724] using wordTrace_append hprefix tailTrace_2789724
  have hstable : (prefixWord ++ tailWord_2789724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789724).length < 2 ^ (prefixWord ++ tailWord_2789724).sum := by decide
  have hdescent : baseEnd_2789724 < baseStart_2789724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789784 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_2789784 : Nat := 118140960795 + 2789784 * 2 ^ 59
def prefixEnd_2789784 : Nat := 4983230072969 + 3 ^ 40 * 2789784 * 2
def baseEnd_2789784 : Nat := 477500038074272730323341

theorem tailTrace_2789784 : CollatzResearch.WordTrace tailWord_2789784 prefixEnd_2789784 477500038074272730323341 := by
  unfold tailWord_2789784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50875890862548250009808203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67834521150064333346410937 50875890862548250009808203)
  ·
    refine ⟨76313836293822375014712305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50875890862548250009808203 76313836293822375014712305)
    ·
      refine ⟨57235377220366781261034229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76313836293822375014712305 57235377220366781261034229)
      ·
        refine ⟨5365816614409385743221959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57235377220366781261034229 5365816614409385743221959)
        ·
          refine ⟨8048724921614078614832939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365816614409385743221959 8048724921614078614832939)
          ·
            refine ⟨12073087382421117922249409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048724921614078614832939 12073087382421117922249409)
            ·
              refine ⟨9054815536815838441687057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12073087382421117922249409 9054815536815838441687057)
              ·
                refine ⟨6791111652611878831265293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9054815536815838441687057 6791111652611878831265293)
                ·
                  refine ⟨2546666869729454561724485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6791111652611878831265293 2546666869729454561724485)
                  ·
                    refine ⟨477500038074272730323341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546666869729454561724485 477500038074272730323341)
                    ·
                      rfl

theorem cell23_2789784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_2789784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789784 prefixEnd_2789784 := by exact prefixLift 2789784
  have htrace : WordTrace (prefixWord ++ tailWord_2789784) baseStart_2789784 baseEnd_2789784 := by
    simpa [prefixWord, tailWord_2789784, baseEnd_2789784] using wordTrace_append hprefix tailTrace_2789784
  have hstable : (prefixWord ++ tailWord_2789784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789784).length < 2 ^ (prefixWord ++ tailWord_2789784).sum := by decide
  have hdescent : baseEnd_2789784 < baseStart_2789784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789794 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2789794 : Nat := 118140960795 + 2789794 * 2 ^ 59
def prefixEnd_2789794 : Nat := 4983230072969 + 3 ^ 40 * 2789794 * 2
def baseEnd_2789794 : Nat := 1432505249029363151844977

theorem tailTrace_2789794 : CollatzResearch.WordTrace tailWord_2789794 prefixEnd_2789794 1432505249029363151844977 := by
  unfold tailWord_2789794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25438036613765067931870109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67834764303373514484986957 25438036613765067931870109)
  ·
    refine ⟨9539263730161900474451291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25438036613765067931870109 9539263730161900474451291)
    ·
      refine ⟨14308895595242850711676937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9539263730161900474451291 14308895595242850711676937)
      ·
        refine ⟨10731671696432138033757703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14308895595242850711676937 10731671696432138033757703)
        ·
          refine ⟨16097507544648207050636555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10731671696432138033757703 16097507544648207050636555)
          ·
            refine ⟨24146261316972310575954833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097507544648207050636555 24146261316972310575954833)
            ·
              refine ⟨18109695987729232931966125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24146261316972310575954833 18109695987729232931966125)
              ·
                refine ⟨6791135995398462349487297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18109695987729232931966125 6791135995398462349487297)
                ·
                  refine ⟨5093351996548846762115473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6791135995398462349487297 5093351996548846762115473)
                  ·
                    refine ⟨3820013997411635071586605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5093351996548846762115473 3820013997411635071586605)
                    ·
                      refine ⟨1432505249029363151844977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820013997411635071586605 1432505249029363151844977)
                      ·
                        rfl

theorem cell23_2789794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2789794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789794 prefixEnd_2789794 := by exact prefixLift 2789794
  have htrace : WordTrace (prefixWord ++ tailWord_2789794) baseStart_2789794 baseEnd_2789794 := by
    simpa [prefixWord, tailWord_2789794, baseEnd_2789794] using wordTrace_append hprefix tailTrace_2789794
  have hstable : (prefixWord ++ tailWord_2789794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789794).length < 2 ^ (prefixWord ++ tailWord_2789794).sum := by decide
  have hdescent : baseEnd_2789794 < baseStart_2789794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789834 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_2789834 : Nat := 118140960795 + 2789834 * 2 ^ 59
def prefixEnd_2789834 : Nat := 4983230072969 + 3 ^ 40 * 2789834 * 2
def baseEnd_2789834 : Nat := 1432525788255542995344793

theorem tailTrace_2789834 : CollatzResearch.WordTrace tailWord_2789834 prefixEnd_2789834 1432525788255542995344793 := by
  unfold tailWord_2789834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25438401343728839639734139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67835736916610239039291037 25438401343728839639734139)
  ·
    refine ⟨38157602015593259459601209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25438401343728839639734139 38157602015593259459601209)
    ·
      refine ⟨28618201511694944594700907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38157602015593259459601209 28618201511694944594700907)
      ·
        refine ⟨42927302267542416892051361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28618201511694944594700907 42927302267542416892051361)
        ·
          refine ⟨32195476700656812669038521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42927302267542416892051361 32195476700656812669038521)
          ·
            refine ⟨24146607525492609501778891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32195476700656812669038521 24146607525492609501778891)
            ·
              refine ⟨36219911288238914252668337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24146607525492609501778891 36219911288238914252668337)
              ·
                refine ⟨27164933466179185689501253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36219911288238914252668337 27164933466179185689501253)
                ·
                  refine ⟨5093425024908597316781485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27164933466179185689501253 5093425024908597316781485)
                  ·
                    refine ⟨1910034384340723993793057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5093425024908597316781485 1910034384340723993793057)
                    ·
                      refine ⟨1432525788255542995344793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910034384340723993793057 1432525788255542995344793)
                      ·
                        rfl

theorem cell23_2789834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_2789834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789834 prefixEnd_2789834 := by exact prefixLift 2789834
  have htrace : WordTrace (prefixWord ++ tailWord_2789834) baseStart_2789834 baseEnd_2789834 := by
    simpa [prefixWord, tailWord_2789834, baseEnd_2789834] using wordTrace_append hprefix tailTrace_2789834
  have hstable : (prefixWord ++ tailWord_2789834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789834).length < 2 ^ (prefixWord ++ tailWord_2789834).sum := by decide
  have hdescent : baseEnd_2789834 < baseStart_2789834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789844 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_2789844 : Nat := 118140960795 + 2789844 * 2 ^ 59
def prefixEnd_2789844 : Nat := 4983230072969 + 3 ^ 40 * 2789844 * 2
def baseEnd_2789844 : Nat := 477510307687362652073249

theorem tailTrace_2789844 : CollatzResearch.WordTrace tailWord_2789844 prefixEnd_2789844 477510307687362652073249 := by
  unfold tailWord_2789844
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876985052439565133400293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67835980069919420177867057 50876985052439565133400293)
  ·
    refine ⟨9539434697332418462512555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50876985052439565133400293 9539434697332418462512555)
    ·
      refine ⟨14309152045998627693768833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9539434697332418462512555 14309152045998627693768833)
      ·
        refine ⟨10731864034498970770326625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14309152045998627693768833 10731864034498970770326625)
        ·
          refine ⟨8048898025874228077744969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10731864034498970770326625 8048898025874228077744969)
          ·
            refine ⟨6036673519405671058308727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8048898025874228077744969 6036673519405671058308727)
            ·
              refine ⟨9055010279108506587463091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036673519405671058308727 9055010279108506587463091)
              ·
                refine ⟨13582515418662759881194637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9055010279108506587463091 13582515418662759881194637)
                ·
                  refine ⟨5093443281998534955447989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13582515418662759881194637 5093443281998534955447989)
                  ·
                    refine ⟨477510307687362652073249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5093443281998534955447989 477510307687362652073249)
                    ·
                      rfl

theorem cell23_2789844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_2789844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789844 prefixEnd_2789844 := by exact prefixLift 2789844
  have htrace : WordTrace (prefixWord ++ tailWord_2789844) baseStart_2789844 baseEnd_2789844 := by
    simpa [prefixWord, tailWord_2789844, baseEnd_2789844] using wordTrace_append hprefix tailTrace_2789844
  have hstable : (prefixWord ++ tailWord_2789844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789844).length < 2 ^ (prefixWord ++ tailWord_2789844).sum := by decide
  have hdescent : baseEnd_2789844 < baseStart_2789844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789857 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2789857 : Nat := 118140960795 + 2789857 * 2 ^ 59
def prefixEnd_2789857 : Nat := 4983230072969 + 3 ^ 40 * 2789857 * 2
def baseEnd_2789857 : Nat := 477512532770198801785729

theorem tailTrace_2789857 : CollatzResearch.WordTrace tailWord_2789857 prefixEnd_2789857 477512532770198801785729 := by
  unfold tailWord_2789857
  simp only [CollatzResearch.WordTrace]
  refine ⟨101754444253832033487023825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67836296169221355658015883 101754444253832033487023825)
  ·
    refine ⟨76315833190374025115267869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101754444253832033487023825 76315833190374025115267869)
    ·
      refine ⟨28618437446390259418225451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76315833190374025115267869 28618437446390259418225451)
      ·
        refine ⟨42927656169585389127338177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28618437446390259418225451 42927656169585389127338177)
        ·
          refine ⟨32195742127189041845503633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42927656169585389127338177 32195742127189041845503633)
          ·
            refine ⟨24146806595391781384127725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32195742127189041845503633 24146806595391781384127725)
            ·
              refine ⟨9055052473271918019047897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24146806595391781384127725 9055052473271918019047897)
              ·
                refine ⟨6791289354953938514285923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9055052473271918019047897 6791289354953938514285923)
                ·
                  refine ⟨10186934032430907771428885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6791289354953938514285923 10186934032430907771428885)
                  ·
                    refine ⟨477512532770198801785729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10186934032430907771428885 477512532770198801785729)
                    ·
                      rfl

theorem cell23_2789857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2789857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789857 prefixEnd_2789857 := by exact prefixLift 2789857
  have htrace : WordTrace (prefixWord ++ tailWord_2789857) baseStart_2789857 baseEnd_2789857 := by
    simpa [prefixWord, tailWord_2789857, baseEnd_2789857] using wordTrace_append hprefix tailTrace_2789857
  have hstable : (prefixWord ++ tailWord_2789857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789857).length < 2 ^ (prefixWord ++ tailWord_2789857).sum := by decide
  have hdescent : baseEnd_2789857 < baseStart_2789857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789914 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2789914 : Nat := 118140960795 + 2789914 * 2 ^ 59
def prefixEnd_2789914 : Nat := 4983230072969 + 3 ^ 40 * 2789914 * 2
def baseEnd_2789914 : Nat := 1432566866707902682344425

theorem tailTrace_2789914 : CollatzResearch.WordTrace tailWord_2789914 prefixEnd_2789914 1432566866707902682344425 := by
  unfold tailWord_2789914
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439130803656383055462199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67837682143083688147899197 25439130803656383055462199)
  ·
    refine ⟨38158696205484574583193299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25439130803656383055462199 38158696205484574583193299)
    ·
      refine ⟨57238044308226861874789949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38158696205484574583193299 57238044308226861874789949)
      ·
        refine ⟨21464266615585073203046231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57238044308226861874789949 21464266615585073203046231)
        ·
          refine ⟨32196399923377609804569347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21464266615585073203046231 32196399923377609804569347)
          ·
            refine ⟨48294599885066414706854021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32196399923377609804569347 48294599885066414706854021)
            ·
              refine ⟨9055237478449952757535129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48294599885066414706854021 9055237478449952757535129)
              ·
                refine ⟨6791428108837464568151347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9055237478449952757535129 6791428108837464568151347)
                ·
                  refine ⟨10187142163256196852227021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6791428108837464568151347 10187142163256196852227021)
                  ·
                    refine ⟨3820178311221073819585133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10187142163256196852227021 3820178311221073819585133)
                    ·
                      refine ⟨1432566866707902682344425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820178311221073819585133 1432566866707902682344425)
                      ·
                        rfl

theorem cell23_2789914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2789914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789914 prefixEnd_2789914 := by exact prefixLift 2789914
  have htrace : WordTrace (prefixWord ++ tailWord_2789914) baseStart_2789914 baseEnd_2789914 := by
    simpa [prefixWord, tailWord_2789914, baseEnd_2789914] using wordTrace_append hprefix tailTrace_2789914
  have hstable : (prefixWord ++ tailWord_2789914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789914).length < 2 ^ (prefixWord ++ tailWord_2789914).sum := by decide
  have hdescent : baseEnd_2789914 < baseStart_2789914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789937 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2789937 : Nat := 118140960795 + 2789937 * 2 ^ 59
def prefixEnd_2789937 : Nat := 4983230072969 + 3 ^ 40 * 2789937 * 2
def baseEnd_2789937 : Nat := 1432578676762956092356819

theorem tailTrace_2789937 : CollatzResearch.WordTrace tailWord_2789937 prefixEnd_2789937 1432578676762956092356819 := by
  unfold tailWord_2789937
  simp only [CollatzResearch.WordTrace]
  refine ⟨101757362093542207149936065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67838241395694804766624043 101757362093542207149936065)
  ·
    refine ⟨76318021570156655362452049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101757362093542207149936065 76318021570156655362452049)
    ·
      refine ⟨57238516177617491521839037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76318021570156655362452049 57238516177617491521839037)
      ·
        refine ⟨21464443566606559320689639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57238516177617491521839037 21464443566606559320689639)
        ·
          refine ⟨32196665349909838981034459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21464443566606559320689639 32196665349909838981034459)
          ·
            refine ⟨48294998024864758471551689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32196665349909838981034459 48294998024864758471551689)
            ·
              refine ⟨36221248518648568853663767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48294998024864758471551689 36221248518648568853663767)
              ·
                refine ⟨54331872777972853280495651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36221248518648568853663767 54331872777972853280495651)
                ·
                  refine ⟨81497809166959279920743477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54331872777972853280495651 81497809166959279920743477)
                  ·
                    refine ⟨7640419609402432492569701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81497809166959279920743477 7640419609402432492569701)
                    ·
                      refine ⟨1432578676762956092356819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7640419609402432492569701 1432578676762956092356819)
                      ·
                        rfl

theorem cell23_2789937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2789937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789937 prefixEnd_2789937 := by exact prefixLift 2789937
  have htrace : WordTrace (prefixWord ++ tailWord_2789937) baseStart_2789937 baseEnd_2789937 := by
    simpa [prefixWord, tailWord_2789937, baseEnd_2789937] using wordTrace_append hprefix tailTrace_2789937
  have hstable : (prefixWord ++ tailWord_2789937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789937).length < 2 ^ (prefixWord ++ tailWord_2789937).sum := by decide
  have hdescent : baseEnd_2789937 < baseStart_2789937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789967 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_2789967 : Nat := 118140960795 + 2789967 * 2 ^ 59
def prefixEnd_2789967 : Nat := 4983230072969 + 3 ^ 40 * 2789967 * 2
def baseEnd_2789967 : Nat := 1432594081182590974981681

theorem tailTrace_2789967 : CollatzResearch.WordTrace tailWord_2789967 prefixEnd_2789967 1432594081182590974981681 := by
  unfold tailWord_2789967
  simp only [CollatzResearch.WordTrace]
  refine ⟨101758456283433522273528155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67838970855622348182352103 101758456283433522273528155)
  ·
    refine ⟨152637684425150283410292233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101758456283433522273528155 152637684425150283410292233)
    ·
      refine ⟨114478263318862712557719175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152637684425150283410292233 114478263318862712557719175)
      ·
        refine ⟨171717394978294068836578763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114478263318862712557719175 171717394978294068836578763)
        ·
          refine ⟨257576092467441103254868145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171717394978294068836578763 257576092467441103254868145)
          ·
            refine ⟨193182069350580827441151109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257576092467441103254868145 193182069350580827441151109)
            ·
              refine ⟨36221638003233905145215833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193182069350580827441151109 36221638003233905145215833)
              ·
                refine ⟨27166228502425428858911875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36221638003233905145215833 27166228502425428858911875)
                ·
                  refine ⟨40749342753638143288367813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27166228502425428858911875 40749342753638143288367813)
                  ·
                    refine ⟨7640501766307151866568965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40749342753638143288367813 7640501766307151866568965)
                    ·
                      refine ⟨1432594081182590974981681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7640501766307151866568965 1432594081182590974981681)
                      ·
                        rfl

theorem cell23_2789967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_2789967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789967 prefixEnd_2789967 := by exact prefixLift 2789967
  have htrace : WordTrace (prefixWord ++ tailWord_2789967) baseStart_2789967 baseEnd_2789967 := by
    simpa [prefixWord, tailWord_2789967, baseEnd_2789967] using wordTrace_append hprefix tailTrace_2789967
  have hstable : (prefixWord ++ tailWord_2789967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789967).length < 2 ^ (prefixWord ++ tailWord_2789967).sum := by decide
  have hdescent : baseEnd_2789967 < baseStart_2789967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789987 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2789987 : Nat := 118140960795 + 2789987 * 2 ^ 59
def prefixEnd_2789987 : Nat := 4983230072969 + 3 ^ 40 * 2789987 * 2
def baseEnd_2789987 : Nat := 1432604350795680896731589

theorem tailTrace_2789987 : CollatzResearch.WordTrace tailWord_2789987 prefixEnd_2789987 1432604350795680896731589 := by
  unfold tailWord_2789987
  simp only [CollatzResearch.WordTrace]
  refine ⟨101759185743361065689256215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67839457162240710459504143 101759185743361065689256215)
  ·
    refine ⟨152638778615041598533884323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101759185743361065689256215 152638778615041598533884323)
    ·
      refine ⟨228958167922562397800826485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152638778615041598533884323 228958167922562397800826485)
      ·
        refine ⟨21464828242740224793827483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228958167922562397800826485 21464828242740224793827483)
        ·
          refine ⟨32197242364110337190741225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21464828242740224793827483 32197242364110337190741225)
          ·
            refine ⟨24147931773082752893055919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32197242364110337190741225 24147931773082752893055919)
            ·
              refine ⟨36221897659624129339583879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24147931773082752893055919 36221897659624129339583879)
              ·
                refine ⟨54332846489436194009375819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36221897659624129339583879 54332846489436194009375819)
                ·
                  refine ⟨81499269734154291014063729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54332846489436194009375819 81499269734154291014063729)
                  ·
                    refine ⟨61124452300615718260547797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81499269734154291014063729 61124452300615718260547797)
                    ·
                      refine ⟨1432604350795680896731589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61124452300615718260547797 1432604350795680896731589)
                      ·
                        rfl

theorem cell23_2789987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2789987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789987 prefixEnd_2789987 := by exact prefixLift 2789987
  have htrace : WordTrace (prefixWord ++ tailWord_2789987) baseStart_2789987 baseEnd_2789987 := by
    simpa [prefixWord, tailWord_2789987, baseEnd_2789987] using wordTrace_append hprefix tailTrace_2789987
  have hstable : (prefixWord ++ tailWord_2789987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789987).length < 2 ^ (prefixWord ++ tailWord_2789987).sum := by decide
  have hdescent : baseEnd_2789987 < baseStart_2789987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2789988 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_2789988 : Nat := 118140960795 + 2789988 * 2 ^ 59
def prefixEnd_2789988 : Nat := 4983230072969 + 3 ^ 40 * 2789988 * 2
def baseEnd_2789988 : Nat := 1432604864276335392819085

theorem tailTrace_2789988 : CollatzResearch.WordTrace tailWord_2789988 prefixEnd_2789988 1432604864276335392819085 := by
  unfold tailWord_2789988
  simp only [CollatzResearch.WordTrace]
  refine ⟨50879611108178721430021309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67839481477571628573361745 50879611108178721430021309)
  ·
    refine ⟨19079854165567020536257991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50879611108178721430021309 19079854165567020536257991)
    ·
      refine ⟨28619781248350530804386987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19079854165567020536257991 28619781248350530804386987)
      ·
        refine ⟨42929671872525796206580481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28619781248350530804386987 42929671872525796206580481)
        ·
          refine ⟨32197253904394347154935361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42929671872525796206580481 32197253904394347154935361)
          ·
            refine ⟨24147940428295760366201521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32197253904394347154935361 24147940428295760366201521)
            ·
              refine ⟨18110955321221820274651141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24147940428295760366201521 18110955321221820274651141)
              ·
                refine ⟨3395804122729091301497089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18110955321221820274651141 3395804122729091301497089)
                ·
                  refine ⟨2546853092046818476122817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395804122729091301497089 2546853092046818476122817)
                  ·
                    refine ⟨1910139819035113857092113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2546853092046818476122817 1910139819035113857092113)
                    ·
                      refine ⟨1432604864276335392819085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910139819035113857092113 1432604864276335392819085)
                      ·
                        rfl

theorem cell23_2789988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_2789988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2789988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2789988 prefixEnd_2789988 := by exact prefixLift 2789988
  have htrace : WordTrace (prefixWord ++ tailWord_2789988) baseStart_2789988 baseEnd_2789988 := by
    simpa [prefixWord, tailWord_2789988, baseEnd_2789988] using wordTrace_append hprefix tailTrace_2789988
  have hstable : (prefixWord ++ tailWord_2789988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2789988).length < 2 ^ (prefixWord ++ tailWord_2789988).sum := by decide
  have hdescent : baseEnd_2789988 < baseStart_2789988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2789988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790007 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 7]
def baseStart_2790007 : Nat := 118140960795 + 2790007 * 2 ^ 59
def prefixEnd_2790007 : Nat := 4983230072969 + 3 ^ 40 * 2790007 * 2
def baseEnd_2790007 : Nat := 477538206802923606160499

theorem tailTrace_2790007 : CollatzResearch.WordTrace tailWord_2790007 prefixEnd_2790007 477538206802923606160499 := by
  unfold tailWord_2790007
  simp only [CollatzResearch.WordTrace]
  refine ⟨101759915203288609104984275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67839943468859072736656183 101759915203288609104984275)
  ·
    refine ⟨152639872804932913657476413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101759915203288609104984275 152639872804932913657476413)
    ·
      refine ⟨57239952301849842621553655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152639872804932913657476413 57239952301849842621553655)
      ·
        refine ⟨85859928452774763932330483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57239952301849842621553655 85859928452774763932330483)
        ·
          refine ⟨128789892679162145898495725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85859928452774763932330483 128789892679162145898495725)
          ·
            refine ⟨48296209754685804711935897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128789892679162145898495725 48296209754685804711935897)
            ·
              refine ⟨36222157316014353533951923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48296209754685804711935897 36222157316014353533951923)
              ·
                refine ⟨54333235974021530300927885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36222157316014353533951923 54333235974021530300927885)
                ·
                  refine ⟨20374963490258073862847957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54333235974021530300927885 20374963490258073862847957)
                  ·
                    refine ⟨477538206802923606160499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20374963490258073862847957 477538206802923606160499)
                    ·
                      rfl

theorem cell23_2790007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_2790007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790007 prefixEnd_2790007 := by exact prefixLift 2790007
  have htrace : WordTrace (prefixWord ++ tailWord_2790007) baseStart_2790007 baseEnd_2790007 := by
    simpa [prefixWord, tailWord_2790007, baseEnd_2790007] using wordTrace_append hprefix tailTrace_2790007
  have hstable : (prefixWord ++ tailWord_2790007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790007).length < 2 ^ (prefixWord ++ tailWord_2790007).sum := by decide
  have hdescent : baseEnd_2790007 < baseStart_2790007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790064 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_2790064 : Nat := 118140960795 + 2790064 * 2 ^ 59
def prefixEnd_2790064 : Nat := 4983230072969 + 3 ^ 40 * 2790064 * 2
def baseEnd_2790064 : Nat := 1432643888806077095468735

theorem tailTrace_2790064 : CollatzResearch.WordTrace tailWord_2790064 prefixEnd_2790064 1432643888806077095468735 := by
  unfold tailWord_2790064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50880997082041053919904623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67841329442721405226539497 50880997082041053919904623)
  ·
    refine ⟨76321495623061580879856935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50880997082041053919904623 76321495623061580879856935)
    ·
      refine ⟨114482243434592371319785403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76321495623061580879856935 114482243434592371319785403)
      ·
        refine ⟨171723365151888556979678105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114482243434592371319785403 171723365151888556979678105)
        ·
          refine ⟨128792523863916417734758579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171723365151888556979678105 128792523863916417734758579)
          ·
            refine ⟨193188785795874626602137869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128792523863916417734758579 193188785795874626602137869)
            ·
              refine ⟨72445794673452984975801701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193188785795874626602137869 72445794673452984975801701)
              ·
                refine ⟨13583586501272434682962819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72445794673452984975801701 13583586501272434682962819)
                ·
                  refine ⟨20375379751908652024444229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13583586501272434682962819 20375379751908652024444229)
                  ·
                    refine ⟨3820383703482872254583293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20375379751908652024444229 3820383703482872254583293)
                    ·
                      refine ⟨1432643888806077095468735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820383703482872254583293 1432643888806077095468735)
                      ·
                        rfl

theorem cell23_2790064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_2790064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790064 prefixEnd_2790064 := by exact prefixLift 2790064
  have htrace : WordTrace (prefixWord ++ tailWord_2790064) baseStart_2790064 baseEnd_2790064 := by
    simpa [prefixWord, tailWord_2790064, baseEnd_2790064] using wordTrace_append hprefix tailTrace_2790064
  have hstable : (prefixWord ++ tailWord_2790064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790064).length < 2 ^ (prefixWord ++ tailWord_2790064).sum := by decide
  have hdescent : baseEnd_2790064 < baseStart_2790064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790088 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 1, 4]
def baseStart_2790088 : Nat := 118140960795 + 2790088 * 2 ^ 59
def prefixEnd_2790088 : Nat := 4983230072969 + 3 ^ 40 * 2790088 * 2
def baseEnd_2790088 : Nat := 477552070780595000522875

theorem tailTrace_2790088 : CollatzResearch.WordTrace tailWord_2790088 prefixEnd_2790088 477552070780595000522875 := by
  unfold tailWord_2790088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50881434757997579969341459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67841913010663439959121945 50881434757997579969341459)
  ·
    refine ⟨76322152136996369954012189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50881434757997579969341459 76322152136996369954012189)
    ·
      refine ⟨28620807051373638732754571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76322152136996369954012189 28620807051373638732754571)
      ·
        refine ⟨42931210577060458099131857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28620807051373638732754571 42931210577060458099131857)
        ·
          refine ⟨32198407932795343574348893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42931210577060458099131857 32198407932795343574348893)
          ·
            refine ⟨12074402974798253840380835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32198407932795343574348893 12074402974798253840380835)
            ·
              refine ⟨18111604462197380760571253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074402974798253840380835 18111604462197380760571253)
              ·
                refine ⟨1697962918331004446303555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18111604462197380760571253 1697962918331004446303555)
                ·
                  refine ⟨2546944377496506669455333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697962918331004446303555 2546944377496506669455333)
                  ·
                    refine ⟨477552070780595000522875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546944377496506669455333 477552070780595000522875)
                    ·
                      rfl

theorem cell23_2790088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_2790088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790088 prefixEnd_2790088 := by exact prefixLift 2790088
  have htrace : WordTrace (prefixWord ++ tailWord_2790088) baseStart_2790088 baseEnd_2790088 := by
    simpa [prefixWord, tailWord_2790088, baseEnd_2790088] using wordTrace_append hprefix tailTrace_2790088
  have hstable : (prefixWord ++ tailWord_2790088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790088).length < 2 ^ (prefixWord ++ tailWord_2790088).sum := by decide
  have hdescent : baseEnd_2790088 < baseStart_2790088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790104 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2790104 : Nat := 118140960795 + 2790104 * 2 ^ 59
def prefixEnd_2790104 : Nat := 4983230072969 + 3 ^ 40 * 2790104 * 2
def baseEnd_2790104 : Nat := 1432664428032256938968551

theorem tailTrace_2790104 : CollatzResearch.WordTrace tailWord_2790104 prefixEnd_2790104 1432664428032256938968551 := by
  unfold tailWord_2790104
  simp only [CollatzResearch.WordTrace]
  refine ⟨50881726541968597335632683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67842302055958129780843577 50881726541968597335632683)
  ·
    refine ⟨76322589812952896003449025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50881726541968597335632683 76322589812952896003449025)
    ·
      refine ⟨57241942359714672002586769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76322589812952896003449025 57241942359714672002586769)
      ·
        refine ⟨42931456769786004001940077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57241942359714672002586769 42931456769786004001940077)
        ·
          refine ⟨16099296288669751500727529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42931456769786004001940077 16099296288669751500727529)
          ·
            refine ⟨12074472216502313625545647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16099296288669751500727529 12074472216502313625545647)
            ·
              refine ⟨18111708324753470438318471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074472216502313625545647 18111708324753470438318471)
              ·
                refine ⟨27167562487130205657477707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18111708324753470438318471 27167562487130205657477707)
                ·
                  refine ⟨40751343730695308486216561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27167562487130205657477707 40751343730695308486216561)
                  ·
                    refine ⟨30563507798021481364662421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40751343730695308486216561 30563507798021481364662421)
                    ·
                      refine ⟨1432664428032256938968551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30563507798021481364662421 1432664428032256938968551)
                      ·
                        rfl

theorem cell23_2790104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2790104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790104 prefixEnd_2790104 := by exact prefixLift 2790104
  have htrace : WordTrace (prefixWord ++ tailWord_2790104) baseStart_2790104 baseEnd_2790104 := by
    simpa [prefixWord, tailWord_2790104, baseEnd_2790104] using wordTrace_append hprefix tailTrace_2790104
  have hstable : (prefixWord ++ tailWord_2790104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790104).length < 2 ^ (prefixWord ++ tailWord_2790104).sum := by decide
  have hdescent : baseEnd_2790104 < baseStart_2790104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790121 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 5, 2]
def baseStart_2790121 : Nat := 118140960795 + 2790121 * 2 ^ 59
def prefixEnd_2790121 : Nat := 4983230072969 + 3 ^ 40 * 2790121 * 2
def baseEnd_2790121 : Nat := 1432673157203383372455973

theorem tailTrace_2790121 : CollatzResearch.WordTrace tailWord_2790121 prefixEnd_2790121 1432673157203383372455973 := by
  unfold tailWord_2790121
  simp only [CollatzResearch.WordTrace]
  refine ⟨101764073124875606574634217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67842715416583737716422811 101764073124875606574634217)
  ·
    refine ⟨76323054843656704930975663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101764073124875606574634217 76323054843656704930975663)
    ·
      refine ⟨114484582265485057396463495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76323054843656704930975663 114484582265485057396463495)
      ·
        refine ⟨171726873398227586094695243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114484582265485057396463495 171726873398227586094695243)
        ·
          refine ⟨257590310097341379142042865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171726873398227586094695243 257590310097341379142042865)
          ·
            refine ⟨193192732573006034356532149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257590310097341379142042865 193192732573006034356532149)
            ·
              refine ⟨18111818678719315720924889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193192732573006034356532149 18111818678719315720924889)
              ·
                refine ⟨13583864009039486790693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18111818678719315720924889 13583864009039486790693667)
                ·
                  refine ⟨20375796013559230186040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13583864009039486790693667 20375796013559230186040501)
                  ·
                    refine ⟨1910230876271177829941297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20375796013559230186040501 1910230876271177829941297)
                    ·
                      refine ⟨1432673157203383372455973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910230876271177829941297 1432673157203383372455973)
                      ·
                        rfl

theorem cell23_2790121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 5, 2].length) (baseStart_2790121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790121 prefixEnd_2790121 := by exact prefixLift 2790121
  have htrace : WordTrace (prefixWord ++ tailWord_2790121) baseStart_2790121 baseEnd_2790121 := by
    simpa [prefixWord, tailWord_2790121, baseEnd_2790121] using wordTrace_append hprefix tailTrace_2790121
  have hstable : (prefixWord ++ tailWord_2790121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790121).length < 2 ^ (prefixWord ++ tailWord_2790121).sum := by decide
  have hdescent : baseEnd_2790121 < baseStart_2790121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790161 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_2790161 : Nat := 118140960795 + 2790161 * 2 ^ 59
def prefixEnd_2790161 : Nat := 4983230072969 + 3 ^ 40 * 2790161 * 2
def baseEnd_2790161 : Nat := 477564565476521071985263

theorem tailTrace_2790161 : CollatzResearch.WordTrace tailWord_2790161 prefixEnd_2790161 477564565476521071985263 := by
  unfold tailWord_2790161
  simp only [CollatzResearch.WordTrace]
  refine ⟨101765532044730693406090337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67843688029820462270726891 101765532044730693406090337)
  ·
    refine ⟨76324149033548020054567753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101765532044730693406090337 76324149033548020054567753)
    ·
      refine ⟨57243111775161015040925815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76324149033548020054567753 57243111775161015040925815)
      ·
        refine ⟨85864667662741522561388723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57243111775161015040925815 85864667662741522561388723)
        ·
          refine ⟨128797001494112283842083085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85864667662741522561388723 128797001494112283842083085)
          ·
            refine ⟨48298875560292106440781157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128797001494112283842083085 48298875560292106440781157)
            ·
              refine ⟨9056039167554769957646467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48298875560292106440781157 9056039167554769957646467)
              ·
                refine ⟨13584058751332154936469701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056039167554769957646467 13584058751332154936469701)
                ·
                  refine ⟨2547011015874779050588069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13584058751332154936469701 2547011015874779050588069)
                  ·
                    refine ⟨477564565476521071985263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547011015874779050588069 477564565476521071985263)
                    ·
                      rfl

theorem cell23_2790161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_2790161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790161 prefixEnd_2790161 := by exact prefixLift 2790161
  have htrace : WordTrace (prefixWord ++ tailWord_2790161) baseStart_2790161 baseEnd_2790161 := by
    simpa [prefixWord, tailWord_2790161, baseEnd_2790161] using wordTrace_append hprefix tailTrace_2790161
  have hstable : (prefixWord ++ tailWord_2790161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790161).length < 2 ^ (prefixWord ++ tailWord_2790161).sum := by decide
  have hdescent : baseEnd_2790161 < baseStart_2790161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790181 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_2790181 : Nat := 118140960795 + 2790181 * 2 ^ 59
def prefixEnd_2790181 : Nat := 4983230072969 + 3 ^ 40 * 2790181 * 2
def baseEnd_2790181 : Nat := 1432703966042653137705697

theorem tailTrace_2790181 : CollatzResearch.WordTrace tailWord_2790181 prefixEnd_2790181 1432703966042653137705697 := by
  unfold tailWord_2790181
  simp only [CollatzResearch.WordTrace]
  refine ⟨101766261504658236821818397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67844174336438824547878931 101766261504658236821818397)
  ·
    refine ⟨38162348064246838808181899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101766261504658236821818397 38162348064246838808181899)
    ·
      refine ⟨57243522096370258212272849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38162348064246838808181899 57243522096370258212272849)
      ·
        refine ⟨42932641572277693659204637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57243522096370258212272849 42932641572277693659204637)
        ·
          refine ⟨16099740589604135122201739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42932641572277693659204637 16099740589604135122201739)
          ·
            refine ⟨24149610884406202683302609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16099740589604135122201739 24149610884406202683302609)
            ·
              refine ⟨18112208163304652012476957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24149610884406202683302609 18112208163304652012476957)
              ·
                refine ⟨6792078061239244504678859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18112208163304652012476957 6792078061239244504678859)
                ·
                  refine ⟨10188117091858866757018289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792078061239244504678859 10188117091858866757018289)
                  ·
                    refine ⟨7641087818894150067763717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10188117091858866757018289 7641087818894150067763717)
                    ·
                      refine ⟨1432703966042653137705697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7641087818894150067763717 1432703966042653137705697)
                      ·
                        rfl

theorem cell23_2790181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_2790181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790181 prefixEnd_2790181 := by exact prefixLift 2790181
  have htrace : WordTrace (prefixWord ++ tailWord_2790181) baseStart_2790181 baseEnd_2790181 := by
    simpa [prefixWord, tailWord_2790181, baseEnd_2790181] using wordTrace_append hprefix tailTrace_2790181
  have hstable : (prefixWord ++ tailWord_2790181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790181).length < 2 ^ (prefixWord ++ tailWord_2790181).sum := by decide
  have hdescent : baseEnd_2790181 < baseStart_2790181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790189 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2790189 : Nat := 118140960795 + 2790189 * 2 ^ 59
def prefixEnd_2790189 : Nat := 4983230072969 + 3 ^ 40 * 2790189 * 2
def baseEnd_2790189 : Nat := 1432708073887889106405661

theorem tailTrace_2790189 : CollatzResearch.WordTrace tailWord_2790189 prefixEnd_2790189 1432708073887889106405661 := by
  unfold tailWord_2790189
  simp only [CollatzResearch.WordTrace]
  refine ⟨101766553288629254188109621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67844368859086169458739747 101766553288629254188109621)
  ·
    refine ⟨9540614370808992580135277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101766553288629254188109621 9540614370808992580135277)
    ·
      refine ⟨3577730389053372217550729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9540614370808992580135277 3577730389053372217550729)
      ·
        refine ⟨2683297791790029163163047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3577730389053372217550729 2683297791790029163163047)
        ·
          refine ⟨4024946687685043744744571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683297791790029163163047 4024946687685043744744571)
          ·
            refine ⟨6037420031527565617116857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024946687685043744744571 6037420031527565617116857)
            ·
              refine ⟨4528065023645674212837643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037420031527565617116857 4528065023645674212837643)
              ·
                refine ⟨6792097535468511319256465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528065023645674212837643 6792097535468511319256465)
                ·
                  refine ⟨5094073151601383489442349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792097535468511319256465 5094073151601383489442349)
                  ·
                    refine ⟨1910277431850518808540881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5094073151601383489442349 1910277431850518808540881)
                    ·
                      refine ⟨1432708073887889106405661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910277431850518808540881 1432708073887889106405661)
                      ·
                        rfl

theorem cell23_2790189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2790189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790189 prefixEnd_2790189 := by exact prefixLift 2790189
  have htrace : WordTrace (prefixWord ++ tailWord_2790189) baseStart_2790189 baseEnd_2790189 := by
    simpa [prefixWord, tailWord_2790189, baseEnd_2790189] using wordTrace_append hprefix tailTrace_2790189
  have hstable : (prefixWord ++ tailWord_2790189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790189).length < 2 ^ (prefixWord ++ tailWord_2790189).sum := by decide
  have hdescent : baseEnd_2790189 < baseStart_2790189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790205 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2790205 : Nat := 118140960795 + 2790205 * 2 ^ 59
def prefixEnd_2790205 : Nat := 4983230072969 + 3 ^ 40 * 2790205 * 2
def baseEnd_2790205 : Nat := 1432716289578361043805587

theorem tailTrace_2790205 : CollatzResearch.WordTrace tailWord_2790205 prefixEnd_2790205 1432716289578361043805587 := by
  unfold tailWord_2790205
  simp only [CollatzResearch.WordTrace]
  refine ⟨101767136856571288920692069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67844757904380859280461379 101767136856571288920692069)
  ·
    refine ⟨19081338160607116672629763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101767136856571288920692069 19081338160607116672629763)
    ·
      refine ⟨28622007240910675008944645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19081338160607116672629763 28622007240910675008944645)
      ·
        refine ⟨5366626357670751564177121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28622007240910675008944645 5366626357670751564177121)
        ·
          refine ⟨4024969768253063673132841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5366626357670751564177121 4024969768253063673132841)
          ·
            refine ⟨3018727326189797754849631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024969768253063673132841 3018727326189797754849631)
            ·
              refine ⟨4528090989284696632274447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018727326189797754849631 4528090989284696632274447)
              ·
                refine ⟨6792136483927044948411671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528090989284696632274447 6792136483927044948411671)
                ·
                  refine ⟨10188204725890567422617507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792136483927044948411671 10188204725890567422617507)
                  ·
                    refine ⟨15282307088835851133926261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10188204725890567422617507 15282307088835851133926261)
                    ·
                      refine ⟨1432716289578361043805587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15282307088835851133926261 1432716289578361043805587)
                      ·
                        rfl

theorem cell23_2790205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2790205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790205 prefixEnd_2790205 := by exact prefixLift 2790205
  have htrace : WordTrace (prefixWord ++ tailWord_2790205) baseStart_2790205 baseEnd_2790205 := by
    simpa [prefixWord, tailWord_2790205, baseEnd_2790205] using wordTrace_append hprefix tailTrace_2790205
  have hstable : (prefixWord ++ tailWord_2790205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790205).length < 2 ^ (prefixWord ++ tailWord_2790205).sum := by decide
  have hdescent : baseEnd_2790205 < baseStart_2790205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790271 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_2790271 : Nat := 118140960795 + 2790271 * 2 ^ 59
def prefixEnd_2790271 : Nat := 4983230072969 + 3 ^ 40 * 2790271 * 2
def baseEnd_2790271 : Nat := 1432750179301557785580283

theorem tailTrace_2790271 : CollatzResearch.WordTrace tailWord_2790271 prefixEnd_2790271 1432750179301557785580283 := by
  unfold tailWord_2790271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101769544074332182192594667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67846362716221454795063111 101769544074332182192594667)
  ·
    refine ⟨152654316111498273288892001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101769544074332182192594667 152654316111498273288892001)
    ·
      refine ⟨114490737083623704966669001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152654316111498273288892001 114490737083623704966669001)
      ·
        refine ⟨85868052812717778725001751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114490737083623704966669001 85868052812717778725001751)
        ·
          refine ⟨128802079219076668087502627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85868052812717778725001751 128802079219076668087502627)
          ·
            refine ⟨193203118828615002131253941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128802079219076668087502627 193203118828615002131253941)
            ·
              refine ⟨18112792390182656449805057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193203118828615002131253941 18112792390182656449805057)
              ·
                refine ⟨13584594292636992337353793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18112792390182656449805057 13584594292636992337353793)
                ·
                  refine ⟨10188445719477744253015345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13584594292636992337353793 10188445719477744253015345)
                  ·
                    refine ⟨7641334289608308189761509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10188445719477744253015345 7641334289608308189761509)
                    ·
                      refine ⟨1432750179301557785580283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7641334289608308189761509 1432750179301557785580283)
                      ·
                        rfl

theorem cell23_2790271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_2790271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790271 prefixEnd_2790271 := by exact prefixLift 2790271
  have htrace : WordTrace (prefixWord ++ tailWord_2790271) baseStart_2790271 baseEnd_2790271 := by
    simpa [prefixWord, tailWord_2790271, baseEnd_2790271] using wordTrace_append hprefix tailTrace_2790271
  have hstable : (prefixWord ++ tailWord_2790271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790271).length < 2 ^ (prefixWord ++ tailWord_2790271).sum := by decide
  have hdescent : baseEnd_2790271 < baseStart_2790271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790275 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 4, 2, 2]
def baseStart_2790275 : Nat := 118140960795 + 2790275 * 2 ^ 59
def prefixEnd_2790275 : Nat := 4983230072969 + 3 ^ 40 * 2790275 * 2
def baseEnd_2790275 : Nat := 1432752233224175769930265

theorem tailTrace_2790275 : CollatzResearch.WordTrace tailWord_2790275 prefixEnd_2790275 1432752233224175769930265 := by
  unfold tailWord_2790275
  simp only [CollatzResearch.WordTrace]
  refine ⟨101769689966317690875740279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67846459977545127250493519 101769689966317690875740279)
  ·
    refine ⟨152654534949476536313610419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101769689966317690875740279 152654534949476536313610419)
    ·
      refine ⟨228981802424214804470415629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152654534949476536313610419 228981802424214804470415629)
      ·
        refine ⟨85868175909080551676405861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228981802424214804470415629 85868175909080551676405861)
        ·
          refine ⟨16100282982952603439326099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85868175909080551676405861 16100282982952603439326099)
          ·
            refine ⟨24150424474428905158989149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16100282982952603439326099 24150424474428905158989149)
            ·
              refine ⟨9056409177910839434620931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24150424474428905158989149 9056409177910839434620931)
              ·
                refine ⟨13584613766866259151931397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056409177910839434620931 13584613766866259151931397)
                ·
                  refine ⟨2547115081287423590987137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13584613766866259151931397 2547115081287423590987137)
                  ·
                    refine ⟨1910336310965567693240353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547115081287423590987137 1910336310965567693240353)
                    ·
                      refine ⟨1432752233224175769930265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910336310965567693240353 1432752233224175769930265)
                      ·
                        rfl

theorem cell23_2790275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_2790275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790275 prefixEnd_2790275 := by exact prefixLift 2790275
  have htrace : WordTrace (prefixWord ++ tailWord_2790275) baseStart_2790275 baseEnd_2790275 := by
    simpa [prefixWord, tailWord_2790275, baseEnd_2790275] using wordTrace_append hprefix tailTrace_2790275
  have hstable : (prefixWord ++ tailWord_2790275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790275).length < 2 ^ (prefixWord ++ tailWord_2790275).sum := by decide
  have hdescent : baseEnd_2790275 < baseStart_2790275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790281 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 7]
def baseStart_2790281 : Nat := 118140960795 + 2790281 * 2 ^ 59
def prefixEnd_2790281 : Nat := 4983230072969 + 3 ^ 40 * 2790281 * 2
def baseEnd_2790281 : Nat := 159195034900900305161693

theorem tailTrace_2790281 : CollatzResearch.WordTrace tailWord_2790281 prefixEnd_2790281 159195034900900305161693 := by
  unfold tailWord_2790281
  simp only [CollatzResearch.WordTrace]
  refine ⟨101769908804295953900458697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67846605869530635933639131 101769908804295953900458697)
  ·
    refine ⟨76327431603221965425344023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101769908804295953900458697 76327431603221965425344023)
    ·
      refine ⟨114491147404832948138016035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76327431603221965425344023 114491147404832948138016035)
      ·
        refine ⟨171736721107249422207024053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114491147404832948138016035 171736721107249422207024053)
        ·
          refine ⟨16100317603804633331908505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171736721107249422207024053 16100317603804633331908505)
          ·
            refine ⟨12075238202853474998931379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16100317603804633331908505 12075238202853474998931379)
            ·
              refine ⟨18112857304280212498397069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12075238202853474998931379 18112857304280212498397069)
              ·
                refine ⟨6792321489105079686898901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18112857304280212498397069 6792321489105079686898901)
                ·
                  refine ⟨159195034900900305161693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6792321489105079686898901 159195034900900305161693)
                  ·
                    rfl

theorem cell23_2790281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_2790281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790281 prefixEnd_2790281 := by exact prefixLift 2790281
  have htrace : WordTrace (prefixWord ++ tailWord_2790281) baseStart_2790281 baseEnd_2790281 := by
    simpa [prefixWord, tailWord_2790281, baseEnd_2790281] using wordTrace_append hprefix tailTrace_2790281
  have hstable : (prefixWord ++ tailWord_2790281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790281).length < 2 ^ (prefixWord ++ tailWord_2790281).sum := by decide
  have hdescent : baseEnd_2790281 < baseStart_2790281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790291 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3]
def baseStart_2790291 : Nat := 118140960795 + 2790291 * 2 ^ 59
def prefixEnd_2790291 : Nat := 4983230072969 + 3 ^ 40 * 2790291 * 2
def baseEnd_2790291 : Nat := 1432760448914647707330191

theorem tailTrace_2790291 : CollatzResearch.WordTrace tailWord_2790291 prefixEnd_2790291 1432760448914647707330191 := by
  unfold tailWord_2790291
  simp only [CollatzResearch.WordTrace]
  refine ⟨101770273534259725608322727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67846849022839817072215151 101770273534259725608322727)
  ·
    refine ⟨152655410301389588412484091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101770273534259725608322727 152655410301389588412484091)
    ·
      refine ⟨228983115452084382618726137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152655410301389588412484091 228983115452084382618726137)
      ·
        refine ⟨171737336589063286964044603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228983115452084382618726137 171737336589063286964044603)
        ·
          refine ⟨257606004883594930446066905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171737336589063286964044603 257606004883594930446066905)
          ·
            refine ⟨193204503662696197834550179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257606004883594930446066905 193204503662696197834550179)
            ·
              refine ⟨289806755494044296751825269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193204503662696197834550179 289806755494044296751825269)
              ·
                refine ⟨27169383327566652820483619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 289806755494044296751825269 27169383327566652820483619)
                ·
                  refine ⟨40754074991349979230725429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27169383327566652820483619 40754074991349979230725429)
                  ·
                    refine ⟨3820694530439060552880509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40754074991349979230725429 3820694530439060552880509)
                    ·
                      refine ⟨1432760448914647707330191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820694530439060552880509 1432760448914647707330191)
                      ·
                        rfl

theorem cell23_2790291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_2790291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790291 prefixEnd_2790291 := by exact prefixLift 2790291
  have htrace : WordTrace (prefixWord ++ tailWord_2790291) baseStart_2790291 baseEnd_2790291 := by
    simpa [prefixWord, tailWord_2790291, baseEnd_2790291] using wordTrace_append hprefix tailTrace_2790291
  have hstable : (prefixWord ++ tailWord_2790291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790291).length < 2 ^ (prefixWord ++ tailWord_2790291).sum := by decide
  have hdescent : baseEnd_2790291 < baseStart_2790291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790328 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_2790328 : Nat := 118140960795 + 2790328 * 2 ^ 59
def prefixEnd_2790328 : Nat := 4983230072969 + 3 ^ 40 * 2790328 * 2
def baseEnd_2790328 : Nat := 477593149232954687522507

theorem tailTrace_2790328 : CollatzResearch.WordTrace tailWord_2790328 prefixEnd_2790328 477593149232954687522507 := by
  unfold tailWord_2790328
  simp only [CollatzResearch.WordTrace]
  refine ⟨50885811517562840463709819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67847748690083787284946425 50885811517562840463709819)
  ·
    refine ⟨76328717276344260695564729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50885811517562840463709819 76328717276344260695564729)
    ·
      refine ⟨57246537957258195521673547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76328717276344260695564729 57246537957258195521673547)
      ·
        refine ⟨85869806935887293282510321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57246537957258195521673547 85869806935887293282510321)
        ·
          refine ⟨64402355201915469961882741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85869806935887293282510321 64402355201915469961882741)
          ·
            refine ⟨6037720800179575308926507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64402355201915469961882741 6037720800179575308926507)
            ·
              refine ⟨9056581200269362963389761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6037720800179575308926507 9056581200269362963389761)
              ·
                refine ⟨6792435900202022222542321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056581200269362963389761 6792435900202022222542321)
                ·
                  refine ⟨5094326925151516666906741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792435900202022222542321 5094326925151516666906741)
                  ·
                    refine ⟨477593149232954687522507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5094326925151516666906741 477593149232954687522507)
                    ·
                      rfl

theorem cell23_2790328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_2790328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790328 prefixEnd_2790328 := by exact prefixLift 2790328
  have htrace : WordTrace (prefixWord ++ tailWord_2790328) baseStart_2790328 baseEnd_2790328 := by
    simpa [prefixWord, tailWord_2790328, baseEnd_2790328] using wordTrace_append hprefix tailTrace_2790328
  have hstable : (prefixWord ++ tailWord_2790328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790328).length < 2 ^ (prefixWord ++ tailWord_2790328).sum := by decide
  have hdescent : baseEnd_2790328 < baseStart_2790328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790348 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2790348 : Nat := 118140960795 + 2790348 * 2 ^ 59
def prefixEnd_2790348 : Nat := 4983230072969 + 3 ^ 40 * 2790348 * 2
def baseEnd_2790348 : Nat := 1432789717311953984317429

theorem tailTrace_2790348 : CollatzResearch.WordTrace tailWord_2790348 prefixEnd_2790348 1432789717311953984317429 := by
  unfold tailWord_2790348
  simp only [CollatzResearch.WordTrace]
  refine ⟨50886176247526612171573849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67848234996702149562098465 50886176247526612171573849)
  ·
    refine ⟨38164632185644959128680387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50886176247526612171573849 38164632185644959128680387)
    ·
      refine ⟨57246948278467438693020581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38164632185644959128680387 57246948278467438693020581)
      ·
        refine ⟨10733802802212644754941359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57246948278467438693020581 10733802802212644754941359)
        ·
          refine ⟨16100704203318967132412039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10733802802212644754941359 16100704203318967132412039)
          ·
            refine ⟨24151056304978450698618059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16100704203318967132412039 24151056304978450698618059)
            ·
              refine ⟨36226584457467676047927089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24151056304978450698618059 36226584457467676047927089)
              ·
                refine ⟨27169938343100757035945317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36226584457467676047927089 27169938343100757035945317)
                ·
                  refine ⟨5094363439331391944239747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27169938343100757035945317 5094363439331391944239747)
                  ·
                    refine ⟨7641545158997087916359621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094363439331391944239747 7641545158997087916359621)
                    ·
                      refine ⟨1432789717311953984317429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7641545158997087916359621 1432789717311953984317429)
                      ·
                        rfl

theorem cell23_2790348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2790348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790348 prefixEnd_2790348 := by exact prefixLift 2790348
  have htrace : WordTrace (prefixWord ++ tailWord_2790348) baseStart_2790348 baseEnd_2790348 := by
    simpa [prefixWord, tailWord_2790348, baseEnd_2790348] using wordTrace_append hprefix tailTrace_2790348
  have hstable : (prefixWord ++ tailWord_2790348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790348).length < 2 ^ (prefixWord ++ tailWord_2790348).sum := by decide
  have hdescent : baseEnd_2790348 < baseStart_2790348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790365 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2790365 : Nat := 118140960795 + 2790365 * 2 ^ 59
def prefixEnd_2790365 : Nat := 4983230072969 + 3 ^ 40 * 2790365 * 2
def baseEnd_2790365 : Nat := 1432798446483080417804851

theorem tailTrace_2790365 : CollatzResearch.WordTrace tailWord_2790365 prefixEnd_2790365 1432798446483080417804851 := by
  unfold tailWord_2790365
  simp only [CollatzResearch.WordTrace]
  refine ⟨101772972535991636246516549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67848648357327757497677699 101772972535991636246516549)
  ·
    refine ⟨19082432350498431796221853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101772972535991636246516549 19082432350498431796221853)
    ·
      refine ⟨7155912131436911923583195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19082432350498431796221853 7155912131436911923583195)
      ·
        refine ⟨10733868197155367885374793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155912131436911923583195 10733868197155367885374793)
        ·
          refine ⟨8050401147866525914031095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10733868197155367885374793 8050401147866525914031095)
          ·
            refine ⟨12075601721799788871046643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050401147866525914031095 12075601721799788871046643)
            ·
              refine ⟨18113402582699683306569965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12075601721799788871046643 18113402582699683306569965)
              ·
                refine ⟨6792525968512381239963737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18113402582699683306569965 6792525968512381239963737)
                ·
                  refine ⟨5094394476384285929972803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792525968512381239963737 5094394476384285929972803)
                  ·
                    refine ⟨7641591714576428894959205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094394476384285929972803 7641591714576428894959205)
                    ·
                      refine ⟨1432798446483080417804851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7641591714576428894959205 1432798446483080417804851)
                      ·
                        rfl

theorem cell23_2790365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2790365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790365 prefixEnd_2790365 := by exact prefixLift 2790365
  have htrace : WordTrace (prefixWord ++ tailWord_2790365) baseStart_2790365 baseEnd_2790365 := by
    simpa [prefixWord, tailWord_2790365, baseEnd_2790365] using wordTrace_append hprefix tailTrace_2790365
  have hstable : (prefixWord ++ tailWord_2790365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790365).length < 2 ^ (prefixWord ++ tailWord_2790365).sum := by decide
  have hdescent : baseEnd_2790365 < baseStart_2790365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790385 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2790385 : Nat := 118140960795 + 2790385 * 2 ^ 59
def prefixEnd_2790385 : Nat := 4983230072969 + 3 ^ 40 * 2790385 * 2
def baseEnd_2790385 : Nat := 1432808716096170339554759

theorem tailTrace_2790385 : CollatzResearch.WordTrace tailWord_2790385 prefixEnd_2790385 1432808716096170339554759 := by
  unfold tailWord_2790385
  simp only [CollatzResearch.WordTrace]
  refine ⟨101773701995919179662244609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67849134663946119774829739 101773701995919179662244609)
  ·
    refine ⟨76330276496939384746683457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101773701995919179662244609 76330276496939384746683457)
    ·
      refine ⟨57247707372704538560012593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76330276496939384746683457 57247707372704538560012593)
      ·
        refine ⟨42935780529528403920009445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57247707372704538560012593 42935780529528403920009445)
        ·
          refine ⟨8050458849286575735001771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42935780529528403920009445 8050458849286575735001771)
          ·
            refine ⟨12075688273929863602502657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050458849286575735001771 12075688273929863602502657)
            ·
              refine ⟨9056766205447397701876993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12075688273929863602502657 9056766205447397701876993)
              ·
                refine ⟨6792574654085548276407745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056766205447397701876993 6792574654085548276407745)
                ·
                  refine ⟨5094430990564161207305809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792574654085548276407745 5094430990564161207305809)
                  ·
                    refine ⟨3820823242923120905479357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094430990564161207305809 3820823242923120905479357)
                    ·
                      refine ⟨1432808716096170339554759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820823242923120905479357 1432808716096170339554759)
                      ·
                        rfl

theorem cell23_2790385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2790385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790385 prefixEnd_2790385 := by exact prefixLift 2790385
  have htrace : WordTrace (prefixWord ++ tailWord_2790385) baseStart_2790385 baseEnd_2790385 := by
    simpa [prefixWord, tailWord_2790385, baseEnd_2790385] using wordTrace_append hprefix tailTrace_2790385
  have hstable : (prefixWord ++ tailWord_2790385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790385).length < 2 ^ (prefixWord ++ tailWord_2790385).sum := by decide
  have hdescent : baseEnd_2790385 < baseStart_2790385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790435 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 1, 5]
def baseStart_2790435 : Nat := 118140960795 + 2790435 * 2 ^ 59
def prefixEnd_2790435 : Nat := 4983230072969 + 3 ^ 40 * 2790435 * 2
def baseEnd_2790435 : Nat := 477611463376298381309843

theorem tailTrace_2790435 : CollatzResearch.WordTrace tailWord_2790435 prefixEnd_2790435 477611463376298381309843 := by
  unfold tailWord_2790435
  simp only [CollatzResearch.WordTrace]
  refine ⟨101775525645738038201564759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67850350430492025467709839 101775525645738038201564759)
  ·
    refine ⟨152663288468607057302347139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101775525645738038201564759 152663288468607057302347139)
    ·
      refine ⟨228994932702910585953520709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152663288468607057302347139 228994932702910585953520709)
      ·
        refine ⟨42936549881795734866285133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228994932702910585953520709 42936549881795734866285133)
        ·
          refine ⟨16101206205673400574856925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42936549881795734866285133 16101206205673400574856925)
          ·
            refine ⟨6037952327127525215571347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16101206205673400574856925 6037952327127525215571347)
            ·
              refine ⟨9056928490691287823357021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6037952327127525215571347 9056928490691287823357021)
              ·
                refine ⟨3396348184009232933758883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9056928490691287823357021 3396348184009232933758883)
                ·
                  refine ⟨5094522276013849400638325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396348184009232933758883 5094522276013849400638325)
                  ·
                    refine ⟨477611463376298381309843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5094522276013849400638325 477611463376298381309843)
                    ·
                      rfl

theorem cell23_2790435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 5].length) (baseStart_2790435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790435 prefixEnd_2790435 := by exact prefixLift 2790435
  have htrace : WordTrace (prefixWord ++ tailWord_2790435) baseStart_2790435 baseEnd_2790435 := by
    simpa [prefixWord, tailWord_2790435, baseEnd_2790435] using wordTrace_append hprefix tailTrace_2790435
  have hstable : (prefixWord ++ tailWord_2790435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790435).length < 2 ^ (prefixWord ++ tailWord_2790435).sum := by decide
  have hdescent : baseEnd_2790435 < baseStart_2790435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790458 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_2790458 : Nat := 118140960795 + 2790458 * 2 ^ 59
def prefixEnd_2790458 : Nat := 4983230072969 + 3 ^ 40 * 2790458 * 2
def baseEnd_2790458 : Nat := 1432846200183948553941923

theorem tailTrace_2790458 : CollatzResearch.WordTrace tailWord_2790458 prefixEnd_2790458 1432846200183948553941923 := by
  unfold tailWord_2790458
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444091131163678282413007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67850909683103142086434685 25444091131163678282413007)
  ·
    refine ⟨38166136696745517423619511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444091131163678282413007 38166136696745517423619511)
    ·
      refine ⟨57249205045118276135429267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38166136696745517423619511 57249205045118276135429267)
      ·
        refine ⟨85873807567677414203143901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57249205045118276135429267 85873807567677414203143901)
        ·
          refine ⟨32202677837879030326178963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85873807567677414203143901 32202677837879030326178963)
          ·
            refine ⟨48304016756818545489268445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32202677837879030326178963 48304016756818545489268445)
            ·
              refine ⟨18114006283806954558475667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48304016756818545489268445 18114006283806954558475667)
              ·
                refine ⟨27171009425710431837713501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114006283806954558475667 27171009425710431837713501)
                ·
                  refine ⟨10189128534641411939142563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27171009425710431837713501 10189128534641411939142563)
                  ·
                    refine ⟨15283692801962117908713845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10189128534641411939142563 15283692801962117908713845)
                    ·
                      refine ⟨1432846200183948553941923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15283692801962117908713845 1432846200183948553941923)
                      ·
                        rfl

theorem cell23_2790458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_2790458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790458 prefixEnd_2790458 := by exact prefixLift 2790458
  have htrace : WordTrace (prefixWord ++ tailWord_2790458) baseStart_2790458 baseEnd_2790458 := by
    simpa [prefixWord, tailWord_2790458, baseEnd_2790458] using wordTrace_append hprefix tailTrace_2790458
  have hstable : (prefixWord ++ tailWord_2790458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790458).length < 2 ^ (prefixWord ++ tailWord_2790458).sum := by decide
  have hdescent : baseEnd_2790458 < baseStart_2790458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790472 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_2790472 : Nat := 118140960795 + 2790472 * 2 ^ 59
def prefixEnd_2790472 : Nat := 4983230072969 + 3 ^ 40 * 2790472 * 2
def baseEnd_2790472 : Nat := 1432853388913111499166859

theorem tailTrace_2790472 : CollatzResearch.WordTrace tailWord_2790472 prefixEnd_2790472 1432853388913111499166859 := by
  unfold tailWord_2790472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50888437573301996760330835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67851250097735995680441113 50888437573301996760330835)
  ·
    refine ⟨76332656359952995140496253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50888437573301996760330835 76332656359952995140496253)
    ·
      refine ⟨28624746134982373177686095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76332656359952995140496253 28624746134982373177686095)
      ·
        refine ⟨42937119202473559766529143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28624746134982373177686095 42937119202473559766529143)
        ·
          refine ⟨64405678803710339649793715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42937119202473559766529143 64405678803710339649793715)
          ·
            refine ⟨96608518205565509474690573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64405678803710339649793715 96608518205565509474690573)
            ·
              refine ⟨36228194327087066053008965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96608518205565509474690573 36228194327087066053008965)
              ·
                refine ⟨6792786436328824884939181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36228194327087066053008965 6792786436328824884939181)
                ·
                  refine ⟨2547294913623309331852193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6792786436328824884939181 2547294913623309331852193)
                  ·
                    refine ⟨1910471185217481998889145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547294913623309331852193 1910471185217481998889145)
                    ·
                      refine ⟨1432853388913111499166859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910471185217481998889145 1432853388913111499166859)
                      ·
                        rfl

theorem cell23_2790472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_2790472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790472 prefixEnd_2790472 := by exact prefixLift 2790472
  have htrace : WordTrace (prefixWord ++ tailWord_2790472) baseStart_2790472 baseEnd_2790472 := by
    simpa [prefixWord, tailWord_2790472, baseEnd_2790472] using wordTrace_append hprefix tailTrace_2790472
  have hstable : (prefixWord ++ tailWord_2790472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790472).length < 2 ^ (prefixWord ++ tailWord_2790472).sum := by decide
  have hdescent : baseEnd_2790472 < baseStart_2790472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790478 : List Nat := [4, 1, 1, 1, 1, 3, 3, 9]
def baseStart_2790478 : Nat := 118140960795 + 2790478 * 2 ^ 59
def prefixEnd_2790478 : Nat := 4983230072969 + 3 ^ 40 * 2790478 * 2
def baseEnd_2790478 : Nat := 53068758140631054655253

theorem tailTrace_2790478 : CollatzResearch.WordTrace tailWord_2790478 prefixEnd_2790478 53068758140631054655253 := by
  unfold tailWord_2790478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722136748072782068172511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67851395989721504363586725 12722136748072782068172511)
  ·
    refine ⟨19083205122109173102258767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722136748072782068172511 19083205122109173102258767)
    ·
      refine ⟨28624807683163759653388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083205122109173102258767 28624807683163759653388151)
      ·
        refine ⟨42937211524745639480082227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28624807683163759653388151 42937211524745639480082227)
        ·
          refine ⟨64405817287118459220123341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42937211524745639480082227 64405817287118459220123341)
          ·
            refine ⟨24152181482669422207546253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64405817287118459220123341 24152181482669422207546253)
            ·
              refine ⟨9057068056001033327829845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24152181482669422207546253 9057068056001033327829845)
              ·
                refine ⟨53068758140631054655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9057068056001033327829845 53068758140631054655253)
                ·
                  rfl

theorem cell23_2790478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_2790478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790478 prefixEnd_2790478 := by exact prefixLift 2790478
  have htrace : WordTrace (prefixWord ++ tailWord_2790478) baseStart_2790478 baseEnd_2790478 := by
    simpa [prefixWord, tailWord_2790478, baseEnd_2790478] using wordTrace_append hprefix tailTrace_2790478
  have hstable : (prefixWord ++ tailWord_2790478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790478).length < 2 ^ (prefixWord ++ tailWord_2790478).sum := by decide
  have hdescent : baseEnd_2790478 < baseStart_2790478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790489 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 1, 2, 2]
def baseStart_2790489 : Nat := 118140960795 + 2790489 * 2 ^ 59
def prefixEnd_2790489 : Nat := 4983230072969 + 3 ^ 40 * 2790489 * 2
def baseEnd_2790489 : Nat := 1432862118084237932654281

theorem tailTrace_2790489 : CollatzResearch.WordTrace tailWord_2790489 prefixEnd_2790489 1432862118084237932654281 := by
  unfold tailWord_2790489
  simp only [CollatzResearch.WordTrace]
  refine ⟨101777495187542405424030521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67851663458361603616020347 101777495187542405424030521)
  ·
    refine ⟨76333121390656804068022891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101777495187542405424030521 76333121390656804068022891)
    ·
      refine ⟨114499682085985206102034337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76333121390656804068022891 114499682085985206102034337)
      ·
        refine ⟨85874761564488904576525753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114499682085985206102034337 85874761564488904576525753)
        ·
          refine ⟨64406071173366678432394315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85874761564488904576525753 64406071173366678432394315)
          ·
            refine ⟨96609106760050017648591473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64406071173366678432394315 96609106760050017648591473)
            ·
              refine ⟨72456830070037513236443605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96609106760050017648591473 72456830070037513236443605)
              ·
                refine ⟨1698206954766504216479147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72456830070037513236443605 1698206954766504216479147)
                ·
                  refine ⟨2547310432149756324718721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698206954766504216479147 2547310432149756324718721)
                  ·
                    refine ⟨1910482824112317243539041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547310432149756324718721 1910482824112317243539041)
                    ·
                      refine ⟨1432862118084237932654281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910482824112317243539041 1432862118084237932654281)
                      ·
                        rfl

theorem cell23_2790489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_2790489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790489 prefixEnd_2790489 := by exact prefixLift 2790489
  have htrace : WordTrace (prefixWord ++ tailWord_2790489) baseStart_2790489 baseEnd_2790489 := by
    simpa [prefixWord, tailWord_2790489, baseEnd_2790489] using wordTrace_append hprefix tailTrace_2790489
  have hstable : (prefixWord ++ tailWord_2790489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790489).length < 2 ^ (prefixWord ++ tailWord_2790489).sum := by decide
  have hdescent : baseEnd_2790489 < baseStart_2790489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790492 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2790492 : Nat := 118140960795 + 2790492 * 2 ^ 59
def prefixEnd_2790492 : Nat := 4983230072969 + 3 ^ 40 * 2790492 * 2
def baseEnd_2790492 : Nat := 1432863658526201420916767

theorem tailTrace_2790492 : CollatzResearch.WordTrace tailWord_2790492 prefixEnd_2790492 1432863658526201420916767 := by
  unfold tailWord_2790492
  simp only [CollatzResearch.WordTrace]
  refine ⟨50888802303265768468194865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67851736404354357957593153 50888802303265768468194865)
  ·
    refine ⟨38166601727449326351146149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50888802303265768468194865 38166601727449326351146149)
    ·
      refine ⟨7156237823896748690839903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38166601727449326351146149 7156237823896748690839903)
      ·
        refine ⟨10734356735845123036259855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7156237823896748690839903 10734356735845123036259855)
        ·
          refine ⟨16101535103767684554389783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734356735845123036259855 16101535103767684554389783)
          ·
            refine ⟨24152302655651526831584675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101535103767684554389783 24152302655651526831584675)
            ·
              refine ⟨36228453983477290247377013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24152302655651526831584675 36228453983477290247377013)
              ·
                refine ⟨3396417560950995960691595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36228453983477290247377013 3396417560950995960691595)
                ·
                  refine ⟨5094626341426493941037393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396417560950995960691595 5094626341426493941037393)
                  ·
                    refine ⟨3820969756069870455778045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094626341426493941037393 3820969756069870455778045)
                    ·
                      refine ⟨1432863658526201420916767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3820969756069870455778045 1432863658526201420916767)
                      ·
                        rfl

theorem cell23_2790492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2790492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790492 prefixEnd_2790492 := by exact prefixLift 2790492
  have htrace : WordTrace (prefixWord ++ tailWord_2790492) baseStart_2790492 baseEnd_2790492 := by
    simpa [prefixWord, tailWord_2790492, baseEnd_2790492] using wordTrace_append hprefix tailTrace_2790492
  have hstable : (prefixWord ++ tailWord_2790492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790492).length < 2 ^ (prefixWord ++ tailWord_2790492).sum := by decide
  have hdescent : baseEnd_2790492 < baseStart_2790492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790506 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2790506 : Nat := 118140960795 + 2790506 * 2 ^ 59
def prefixEnd_2790506 : Nat := 4983230072969 + 3 ^ 40 * 2790506 * 2
def baseEnd_2790506 : Nat := 1432870847255364366141703

theorem tailTrace_2790506 : CollatzResearch.WordTrace tailWord_2790506 prefixEnd_2790506 1432870847255364366141703 := by
  unfold tailWord_2790506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444528807120204331849843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67852076818987211551599581 25444528807120204331849843)
  ·
    refine ⟨38166793210680306497774765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444528807120204331849843 38166793210680306497774765)
    ·
      refine ⟨14312547454005114936665537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38166793210680306497774765 14312547454005114936665537)
      ·
        refine ⟨10734410590503836202499153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312547454005114936665537 10734410590503836202499153)
        ·
          refine ⟨8050807942877877151874365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10734410590503836202499153 8050807942877877151874365)
          ·
            refine ⟨3019052978579203931952887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8050807942877877151874365 3019052978579203931952887)
            ·
              refine ⟨4528579467868805897929331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019052978579203931952887 4528579467868805897929331)
              ·
                refine ⟨6792869201803208846893997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528579467868805897929331 6792869201803208846893997)
                ·
                  refine ⟨2547325950676203317585249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6792869201803208846893997 2547325950676203317585249)
                  ·
                    refine ⟨1910494463007152488188937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547325950676203317585249 1910494463007152488188937)
                    ·
                      refine ⟨1432870847255364366141703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910494463007152488188937 1432870847255364366141703)
                      ·
                        rfl

theorem cell23_2790506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2790506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790506 prefixEnd_2790506 := by exact prefixLift 2790506
  have htrace : WordTrace (prefixWord ++ tailWord_2790506) baseStart_2790506 baseEnd_2790506 := by
    simpa [prefixWord, tailWord_2790506, baseEnd_2790506] using wordTrace_append hprefix tailTrace_2790506
  have hstable : (prefixWord ++ tailWord_2790506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790506).length < 2 ^ (prefixWord ++ tailWord_2790506).sum := by decide
  have hdescent : baseEnd_2790506 < baseStart_2790506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790508 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_2790508 : Nat := 118140960795 + 2790508 * 2 ^ 59
def prefixEnd_2790508 : Nat := 4983230072969 + 3 ^ 40 * 2790508 * 2
def baseEnd_2790508 : Nat := 477623958072224452772231

theorem tailTrace_2790508 : CollatzResearch.WordTrace tailWord_2790508 prefixEnd_2790508 477623958072224452772231 := by
  unfold tailWord_2790508
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889094087236785834486089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67852125449649047779314785 50889094087236785834486089)
  ·
    refine ⟨38166820565427589375864567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50889094087236785834486089 38166820565427589375864567)
    ·
      refine ⟨57250230848141384063796851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38166820565427589375864567 57250230848141384063796851)
      ·
        refine ⟨85875346272212076095695277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57250230848141384063796851 85875346272212076095695277)
        ·
          refine ⟨32203254852079528535885729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85875346272212076095695277 32203254852079528535885729)
          ·
            refine ⟨24152441139059646401914297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32203254852079528535885729 24152441139059646401914297)
            ·
              refine ⟨18114330854294734801435723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24152441139059646401914297 18114330854294734801435723)
              ·
                refine ⟨27171496281442102202153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114330854294734801435723 27171496281442102202153585)
                ·
                  refine ⟨20378622211081576651615189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27171496281442102202153585 20378622211081576651615189)
                  ·
                    refine ⟨477623958072224452772231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20378622211081576651615189 477623958072224452772231)
                    ·
                      rfl

theorem cell23_2790508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_2790508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790508 prefixEnd_2790508 := by exact prefixLift 2790508
  have htrace : WordTrace (prefixWord ++ tailWord_2790508) baseStart_2790508 baseEnd_2790508 := by
    simpa [prefixWord, tailWord_2790508, baseEnd_2790508] using wordTrace_append hprefix tailTrace_2790508
  have hstable : (prefixWord ++ tailWord_2790508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790508).length < 2 ^ (prefixWord ++ tailWord_2790508).sum := by decide
  have hdescent : baseEnd_2790508 < baseStart_2790508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790565 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_2790565 : Nat := 118140960795 + 2790565 * 2 ^ 59
def prefixEnd_2790565 : Nat := 4983230072969 + 3 ^ 40 * 2790565 * 2
def baseEnd_2790565 : Nat := 1432901142613979635303931

theorem tailTrace_2790565 : CollatzResearch.WordTrace tailWord_2790565 prefixEnd_2790565 1432901142613979635303931 := by
  unfold tailWord_2790565
  simp only [CollatzResearch.WordTrace]
  refine ⟨101780267135267070403797149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67853511423511380269198099 101780267135267070403797149)
  ·
    refine ⟨38167600175725151401423931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101780267135267070403797149 38167600175725151401423931)
    ·
      refine ⟨57251400263587727102135897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38167600175725151401423931 57251400263587727102135897)
      ·
        refine ⟨42938550197690795326601923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57251400263587727102135897 42938550197690795326601923)
        ·
          refine ⟨64407825296536192989902885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42938550197690795326601923 64407825296536192989902885)
          ·
            refine ⟨12076467243100536185606791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64407825296536192989902885 12076467243100536185606791)
            ·
              refine ⟨18114700864650804278410187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076467243100536185606791 18114700864650804278410187)
              ·
                refine ⟨27172051296976206417615281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114700864650804278410187 27172051296976206417615281)
                ·
                  refine ⟨20379038472732154813211461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27172051296976206417615281 20379038472732154813211461)
                  ·
                    refine ⟨3821069713637279027477149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20379038472732154813211461 3821069713637279027477149)
                    ·
                      refine ⟨1432901142613979635303931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821069713637279027477149 1432901142613979635303931)
                      ·
                        rfl

theorem cell23_2790565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_2790565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790565 prefixEnd_2790565 := by exact prefixLift 2790565
  have htrace : WordTrace (prefixWord ++ tailWord_2790565) baseStart_2790565 baseEnd_2790565 := by
    simpa [prefixWord, tailWord_2790565, baseEnd_2790565] using wordTrace_append hprefix tailTrace_2790565
  have hstable : (prefixWord ++ tailWord_2790565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790565).length < 2 ^ (prefixWord ++ tailWord_2790565).sum := by decide
  have hdescent : baseEnd_2790565 < baseStart_2790565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790579 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 2, 2, 2]
def baseStart_2790579 : Nat := 118140960795 + 2790579 * 2 ^ 59
def prefixEnd_2790579 : Nat := 4983230072969 + 3 ^ 40 * 2790579 * 2
def baseEnd_2790579 : Nat := 1432908331343142580528867

theorem tailTrace_2790579 : CollatzResearch.WordTrace tailWord_2790579 prefixEnd_2790579 1432908331343142580528867 := by
  unfold tailWord_2790579
  simp only [CollatzResearch.WordTrace]
  refine ⟨101780777757216350794806791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67853851838144233863204527 101780777757216350794806791)
  ·
    refine ⟨152671166635824526192210187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101780777757216350794806791 152671166635824526192210187)
    ·
      refine ⟨229006749953736789288315281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152671166635824526192210187 229006749953736789288315281)
      ·
        refine ⟨171755062465302591966236461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229006749953736789288315281 171755062465302591966236461)
        ·
          refine ⟨64408148424488471987338673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171755062465302591966236461 64408148424488471987338673)
          ·
            refine ⟨48306111318366353990504005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64408148424488471987338673 48306111318366353990504005)
            ·
              refine ⟨9057395872193691373219501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48306111318366353990504005 9057395872193691373219501)
              ·
                refine ⟨3396523452072634264957313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9057395872193691373219501 3396523452072634264957313)
                ·
                  refine ⟨2547392589054475698717985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396523452072634264957313 2547392589054475698717985)
                  ·
                    refine ⟨1910544441790856774038489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547392589054475698717985 1910544441790856774038489)
                    ·
                      refine ⟨1432908331343142580528867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910544441790856774038489 1432908331343142580528867)
                      ·
                        rfl

theorem cell23_2790579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 2, 2].length) (baseStart_2790579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790579 prefixEnd_2790579 := by exact prefixLift 2790579
  have htrace : WordTrace (prefixWord ++ tailWord_2790579) baseStart_2790579 baseEnd_2790579 := by
    simpa [prefixWord, tailWord_2790579, baseEnd_2790579] using wordTrace_append hprefix tailTrace_2790579
  have hstable : (prefixWord ++ tailWord_2790579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790579).length < 2 ^ (prefixWord ++ tailWord_2790579).sum := by decide
  have hdescent : baseEnd_2790579 < baseStart_2790579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790585 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 7]
def baseStart_2790585 : Nat := 118140960795 + 2790585 * 2 ^ 59
def prefixEnd_2790585 : Nat := 4983230072969 + 3 ^ 40 * 2790585 * 2
def baseEnd_2790585 : Nat := 159212379136341061894871

theorem tailTrace_2790585 : CollatzResearch.WordTrace tailWord_2790585 prefixEnd_2790585 159212379136341061894871 := by
  unfold tailWord_2790585
  simp only [CollatzResearch.WordTrace]
  refine ⟨101780996595194613819525209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67853997730129742546350139 101780996595194613819525209)
  ·
    refine ⟨76335747446395960364643907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101780996595194613819525209 76335747446395960364643907)
    ·
      refine ⟨114503621169593940546965861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76335747446395960364643907 114503621169593940546965861)
      ·
        refine ⟨21469428969298863852556099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114503621169593940546965861 21469428969298863852556099)
        ·
          refine ⟨32204143453948295778834149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21469428969298863852556099 32204143453948295778834149)
          ·
            refine ⟨6038276897615305458531403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32204143453948295778834149 6038276897615305458531403)
            ·
              refine ⟨9057415346422958187797105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038276897615305458531403 9057415346422958187797105)
              ·
                refine ⟨6793061509817218640847829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9057415346422958187797105 6793061509817218640847829)
                ·
                  refine ⟨159212379136341061894871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6793061509817218640847829 159212379136341061894871)
                  ·
                    rfl

theorem cell23_2790585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_2790585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790585 prefixEnd_2790585 := by exact prefixLift 2790585
  have htrace : WordTrace (prefixWord ++ tailWord_2790585) baseStart_2790585 baseEnd_2790585 := by
    simpa [prefixWord, tailWord_2790585, baseEnd_2790585] using wordTrace_append hprefix tailTrace_2790585
  have hstable : (prefixWord ++ tailWord_2790585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790585).length < 2 ^ (prefixWord ++ tailWord_2790585).sum := by decide
  have hdescent : baseEnd_2790585 < baseStart_2790585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790602 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_2790602 : Nat := 118140960795 + 2790602 * 2 ^ 59
def prefixEnd_2790602 : Nat := 4983230072969 + 3 ^ 40 * 2790602 * 2
def baseEnd_2790602 : Nat := 159213349044243998949029

theorem tailTrace_2790602 : CollatzResearch.WordTrace tailWord_2790602 prefixEnd_2790602 159213349044243998949029 := by
  unfold tailWord_2790602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445404159033256430723515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67854411090755350481929373 25445404159033256430723515)
  ·
    refine ⟨38168106238549884646085273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25445404159033256430723515 38168106238549884646085273)
    ·
      refine ⟨28626079678912413484563955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38168106238549884646085273 28626079678912413484563955)
      ·
        refine ⟨42939119518368620226845933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28626079678912413484563955 42939119518368620226845933)
        ·
          refine ⟨16102169819388232585067225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42939119518368620226845933 16102169819388232585067225)
          ·
            refine ⟨12076627364541174438800419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16102169819388232585067225 12076627364541174438800419)
            ·
              refine ⟨18114941046811761658200629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076627364541174438800419 18114941046811761658200629)
              ·
                refine ⟨1698275723138602655456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18114941046811761658200629 1698275723138602655456309)
                ·
                  refine ⟨159213349044243998949029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698275723138602655456309 159213349044243998949029)
                  ·
                    rfl

theorem cell23_2790602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_2790602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790602 prefixEnd_2790602 := by exact prefixLift 2790602
  have htrace : WordTrace (prefixWord ++ tailWord_2790602) baseStart_2790602 baseEnd_2790602 := by
    simpa [prefixWord, tailWord_2790602, baseEnd_2790602] using wordTrace_append hprefix tailTrace_2790602
  have hstable : (prefixWord ++ tailWord_2790602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790602).length < 2 ^ (prefixWord ++ tailWord_2790602).sum := by decide
  have hdescent : baseEnd_2790602 < baseStart_2790602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790613 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2790613 : Nat := 118140960795 + 2790613 * 2 ^ 59
def prefixEnd_2790613 : Nat := 4983230072969 + 3 ^ 40 * 2790613 * 2
def baseEnd_2790613 : Nat := 1432925789685395447503711

theorem tailTrace_2790613 : CollatzResearch.WordTrace tailWord_2790613 prefixEnd_2790613 1432925789685395447503711 := by
  unfold tailWord_2790613
  simp only [CollatzResearch.WordTrace]
  refine ⟨101782017839093174601544493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67854678559395449734362995 101782017839093174601544493)
  ·
    refine ⟨38168256689659940475579185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101782017839093174601544493 38168256689659940475579185)
    ·
      refine ⟨28626192517244955356684389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38168256689659940475579185 28626192517244955356684389)
      ·
        refine ⟨5367411096983429129378323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28626192517244955356684389 5367411096983429129378323)
        ·
          refine ⟨8051116645475143694067485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367411096983429129378323 8051116645475143694067485)
          ·
            refine ⟨3019168742053178885275307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8051116645475143694067485 3019168742053178885275307)
            ·
              refine ⟨4528753113079768327912961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019168742053178885275307 4528753113079768327912961)
              ·
                refine ⟨3396564834809826245934721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528753113079768327912961 3396564834809826245934721)
                ·
                  refine ⟨2547423626107369684451041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396564834809826245934721 2547423626107369684451041)
                  ·
                    refine ⟨1910567719580527263338281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547423626107369684451041 1910567719580527263338281)
                    ·
                      refine ⟨1432925789685395447503711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910567719580527263338281 1432925789685395447503711)
                      ·
                        rfl

theorem cell23_2790613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2790613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790613 prefixEnd_2790613 := by exact prefixLift 2790613
  have htrace : WordTrace (prefixWord ++ tailWord_2790613) baseStart_2790613 baseEnd_2790613 := by
    simpa [prefixWord, tailWord_2790613, baseEnd_2790613] using wordTrace_append hprefix tailTrace_2790613
  have hstable : (prefixWord ++ tailWord_2790613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790613).length < 2 ^ (prefixWord ++ tailWord_2790613).sum := by decide
  have hdescent : baseEnd_2790613 < baseStart_2790613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790615 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 2, 5]
def baseStart_2790615 : Nat := 118140960795 + 2790615 * 2 ^ 59
def prefixEnd_2790615 : Nat := 4983230072969 + 3 ^ 40 * 2790615 * 2
def baseEnd_2790615 : Nat := 477642272215568146559567

theorem tailTrace_2790615 : CollatzResearch.WordTrace tailWord_2790615 prefixEnd_2790615 477642272215568146559567 := by
  unfold tailWord_2790615
  simp only [CollatzResearch.WordTrace]
  refine ⟨101782090785085928943117299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67854727190057285962078199 101782090785085928943117299)
  ·
    refine ⟨152673136177628893414675949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101782090785085928943117299 152673136177628893414675949)
    ·
      refine ⟨57252426066610835030503481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152673136177628893414675949 57252426066610835030503481)
      ·
        refine ⟨42939319549958126272877611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57252426066610835030503481 42939319549958126272877611)
        ·
          refine ⟨64408979324937189409316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42939319549958126272877611 64408979324937189409316417)
          ·
            refine ⟨48306734493702892056987313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64408979324937189409316417 48306734493702892056987313)
            ·
              refine ⟨36230050870277169042740485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48306734493702892056987313 36230050870277169042740485)
              ·
                refine ⟨6793134538176969195513841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36230050870277169042740485 6793134538176969195513841)
                ·
                  refine ⟨5094850903632726896635381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793134538176969195513841 5094850903632726896635381)
                  ·
                    refine ⟨477642272215568146559567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5094850903632726896635381 477642272215568146559567)
                    ·
                      rfl

theorem cell23_2790615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_2790615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790615 prefixEnd_2790615 := by exact prefixLift 2790615
  have htrace : WordTrace (prefixWord ++ tailWord_2790615) baseStart_2790615 baseEnd_2790615 := by
    simpa [prefixWord, tailWord_2790615, baseEnd_2790615] using wordTrace_append hprefix tailTrace_2790615
  have hstable : (prefixWord ++ tailWord_2790615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790615).length < 2 ^ (prefixWord ++ tailWord_2790615).sum := by decide
  have hdescent : baseEnd_2790615 < baseStart_2790615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790635 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_2790635 : Nat := 118140960795 + 2790635 * 2 ^ 59
def prefixEnd_2790635 : Nat := 4983230072969 + 3 ^ 40 * 2790635 * 2
def baseEnd_2790635 : Nat := 1432937086259794361428609

theorem tailTrace_2790635 : CollatzResearch.WordTrace tailWord_2790635 prefixEnd_2790635 1432937086259794361428609 := by
  unfold tailWord_2790635
  simp only [CollatzResearch.WordTrace]
  refine ⟨101782820245013472358845359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67855213496675648239230239 101782820245013472358845359)
  ·
    refine ⟨152674230367520208538268039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101782820245013472358845359 152674230367520208538268039)
    ·
      refine ⟨229011345551280312807402059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152674230367520208538268039 229011345551280312807402059)
      ·
        refine ⟨343517018326920469211103089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229011345551280312807402059 343517018326920469211103089)
        ·
          refine ⟨257637763745190351908327317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343517018326920469211103089 257637763745190351908327317)
          ·
            refine ⟨12076770175555797745702843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 257637763745190351908327317 12076770175555797745702843)
            ·
              refine ⟨18115155263333696618554265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076770175555797745702843 18115155263333696618554265)
              ·
                refine ⟨13586366447500272463915699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18115155263333696618554265 13586366447500272463915699)
                ·
                  refine ⟨20379549671250408695873549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13586366447500272463915699 20379549671250408695873549)
                  ·
                    refine ⟨7642331126718903260952581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20379549671250408695873549 7642331126718903260952581)
                    ·
                      refine ⟨1432937086259794361428609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7642331126718903260952581 1432937086259794361428609)
                      ·
                        rfl

theorem cell23_2790635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_2790635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790635 prefixEnd_2790635 := by exact prefixLift 2790635
  have htrace : WordTrace (prefixWord ++ tailWord_2790635) baseStart_2790635 baseEnd_2790635 := by
    simpa [prefixWord, tailWord_2790635, baseEnd_2790635] using wordTrace_append hprefix tailTrace_2790635
  have hstable : (prefixWord ++ tailWord_2790635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790635).length < 2 ^ (prefixWord ++ tailWord_2790635).sum := by decide
  have hdescent : baseEnd_2790635 < baseStart_2790635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790692 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2790692 : Nat := 118140960795 + 2790692 * 2 ^ 59
def prefixEnd_2790692 : Nat := 4983230072969 + 3 ^ 40 * 2790692 * 2
def baseEnd_2790692 : Nat := 159218483850788959823983

theorem tailTrace_2790692 : CollatzResearch.WordTrace tailWord_2790692 prefixEnd_2790692 159218483850788959823983 := by
  unfold tailWord_2790692
  simp only [CollatzResearch.WordTrace]
  refine ⟨50892449602903485546835165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67856599470537980729113553 50892449602903485546835165)
  ·
    refine ⟨19084668601088807080063187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50892449602903485546835165 19084668601088807080063187)
    ·
      refine ⟨28627002901633210620094781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19084668601088807080063187 28627002901633210620094781)
      ·
        refine ⟨10735126088112453982535543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28627002901633210620094781 10735126088112453982535543)
        ·
          refine ⟨16102689132168680973803315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735126088112453982535543 16102689132168680973803315)
          ·
            refine ⟨24154033698253021460704973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16102689132168680973803315 24154033698253021460704973)
            ·
              refine ⟨9057762636844883047764365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24154033698253021460704973 9057762636844883047764365)
              ·
                refine ⟨3396660988816831142911637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9057762636844883047764365 3396660988816831142911637)
                ·
                  refine ⟨159218483850788959823983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3396660988816831142911637 159218483850788959823983)
                  ·
                    rfl

theorem cell23_2790692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2790692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790692 prefixEnd_2790692 := by exact prefixLift 2790692
  have htrace : WordTrace (prefixWord ++ tailWord_2790692) baseStart_2790692 baseEnd_2790692 := by
    simpa [prefixWord, tailWord_2790692, baseEnd_2790692] using wordTrace_append hprefix tailTrace_2790692
  have hstable : (prefixWord ++ tailWord_2790692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790692).length < 2 ^ (prefixWord ++ tailWord_2790692).sum := by decide
  have hdescent : baseEnd_2790692 < baseStart_2790692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790729 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 2, 3, 2]
def baseStart_2790729 : Nat := 118140960795 + 2790729 * 2 ^ 59
def prefixEnd_2790729 : Nat := 4983230072969 + 3 ^ 40 * 2790729 * 2
def baseEnd_2790729 : Nat := 1432985353441316993653177

theorem tailTrace_2790729 : CollatzResearch.WordTrace tailWord_2790729 prefixEnd_2790729 1432985353441316993653177 := by
  unfold tailWord_2790729
  simp only [CollatzResearch.WordTrace]
  refine ⟨101786248706672926412767241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67857499137781950941844827 101786248706672926412767241)
  ·
    refine ⟨76339686530004694809575431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101786248706672926412767241 76339686530004694809575431)
    ·
      refine ⟨114509529795007042214363147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76339686530004694809575431 114509529795007042214363147)
      ·
        refine ⟨171764294692510563321544721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114509529795007042214363147 171764294692510563321544721)
        ·
          refine ⟨128823221019382922491158541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171764294692510563321544721 128823221019382922491158541)
          ·
            refine ⟨48308707882268595934184453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128823221019382922491158541 48308707882268595934184453)
            ·
              refine ⟨9057882727925361737659585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48308707882268595934184453 9057882727925361737659585)
              ·
                refine ⟨6793412045944021303244689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9057882727925361737659585 6793412045944021303244689)
                ·
                  refine ⟨5095059034458015977433517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793412045944021303244689 5095059034458015977433517)
                  ·
                    refine ⟨1910647137921755991537569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5095059034458015977433517 1910647137921755991537569)
                    ·
                      refine ⟨1432985353441316993653177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910647137921755991537569 1432985353441316993653177)
                      ·
                        rfl

theorem cell23_2790729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 3, 2].length) (baseStart_2790729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790729 prefixEnd_2790729 := by exact prefixLift 2790729
  have htrace : WordTrace (prefixWord ++ tailWord_2790729) baseStart_2790729 baseEnd_2790729 := by
    simpa [prefixWord, tailWord_2790729, baseEnd_2790729] using wordTrace_append hprefix tailTrace_2790729
  have hstable : (prefixWord ++ tailWord_2790729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790729).length < 2 ^ (prefixWord ++ tailWord_2790729).sum := by decide
  have hdescent : baseEnd_2790729 < baseStart_2790729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790736 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 1, 1, 3]
def baseStart_2790736 : Nat := 118140960795 + 2790736 * 2 ^ 59
def prefixEnd_2790736 : Nat := 4983230072969 + 3 ^ 40 * 2790736 * 2
def baseEnd_2790736 : Nat := 1432988947805898466265645

theorem tailTrace_2790736 : CollatzResearch.WordTrace tailWord_2790736 prefixEnd_2790736 1432988947805898466265645 := by
  unfold tailWord_2790736
  simp only [CollatzResearch.WordTrace]
  refine ⟨50893252008823783304136031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67857669345098377738848041 50893252008823783304136031)
  ·
    refine ⟨76339878013235674956204047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50893252008823783304136031 76339878013235674956204047)
    ·
      refine ⟨114509817019853512434306071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76339878013235674956204047 114509817019853512434306071)
      ·
        refine ⟨171764725529780268651459107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114509817019853512434306071 171764725529780268651459107)
        ·
          refine ⟨257647088294670402977188661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171764725529780268651459107 257647088294670402977188661)
          ·
            refine ⟨24154414527625350279111437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257647088294670402977188661 24154414527625350279111437)
            ·
              refine ⟨9057905447859506354666789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24154414527625350279111437 9057905447859506354666789)
              ·
                refine ⟨1698357271473657441500023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9057905447859506354666789 1698357271473657441500023)
                ·
                  refine ⟨2547535907210486162250035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698357271473657441500023 2547535907210486162250035)
                  ·
                    refine ⟨3821303860815729243375053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547535907210486162250035 3821303860815729243375053)
                    ·
                      refine ⟨1432988947805898466265645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821303860815729243375053 1432988947805898466265645)
                      ·
                        rfl

theorem cell23_2790736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 1, 3].length) (baseStart_2790736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790736 prefixEnd_2790736 := by exact prefixLift 2790736
  have htrace : WordTrace (prefixWord ++ tailWord_2790736) baseStart_2790736 baseEnd_2790736 := by
    simpa [prefixWord, tailWord_2790736, baseEnd_2790736] using wordTrace_append hprefix tailTrace_2790736
  have hstable : (prefixWord ++ tailWord_2790736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790736).length < 2 ^ (prefixWord ++ tailWord_2790736).sum := by decide
  have hdescent : baseEnd_2790736 < baseStart_2790736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790752 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_2790752 : Nat := 118140960795 + 2790752 * 2 ^ 59
def prefixEnd_2790752 : Nat := 4983230072969 + 3 ^ 40 * 2790752 * 2
def baseEnd_2790752 : Nat := 477665721165456801221857

theorem tailTrace_2790752 : CollatzResearch.WordTrace tailWord_2790752 prefixEnd_2790752 477665721165456801221857 := by
  unfold tailWord_2790752
  simp only [CollatzResearch.WordTrace]
  refine ⟨50893543792794800670427255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67858058390393067560569673 50893543792794800670427255)
  ·
    refine ⟨76340315689192201005640883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50893543792794800670427255 76340315689192201005640883)
    ·
      refine ⟨114510473533788301508461325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76340315689192201005640883 114510473533788301508461325)
      ·
        refine ⟨42941427575170613065672997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114510473533788301508461325 42941427575170613065672997)
        ·
          refine ⟨8051517670344489949813687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42941427575170613065672997 8051517670344489949813687)
          ·
            refine ⟨12077276505516734924720531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8051517670344489949813687 12077276505516734924720531)
            ·
              refine ⟨18115914758275102387080797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12077276505516734924720531 18115914758275102387080797)
              ·
                refine ⟨6793468034353163395155299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18115914758275102387080797 6793468034353163395155299)
                ·
                  refine ⟨10190202051529745092732949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793468034353163395155299 10190202051529745092732949)
                  ·
                    refine ⟨477665721165456801221857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10190202051529745092732949 477665721165456801221857)
                    ·
                      rfl

theorem cell23_2790752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_2790752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790752 prefixEnd_2790752 := by exact prefixLift 2790752
  have htrace : WordTrace (prefixWord ++ tailWord_2790752) baseStart_2790752 baseEnd_2790752 := by
    simpa [prefixWord, tailWord_2790752, baseEnd_2790752] using wordTrace_append hprefix tailTrace_2790752
  have hstable : (prefixWord ++ tailWord_2790752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790752).length < 2 ^ (prefixWord ++ tailWord_2790752).sum := by decide
  have hdescent : baseEnd_2790752 < baseStart_2790752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790773 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2790773 : Nat := 118140960795 + 2790773 * 2 ^ 59
def prefixEnd_2790773 : Nat := 4983230072969 + 3 ^ 40 * 2790773 * 2
def baseEnd_2790773 : Nat := 477669315530038273834325

theorem tailTrace_2790773 : CollatzResearch.WordTrace tailWord_2790773 prefixEnd_2790773 477669315530038273834325 := by
  unfold tailWord_2790773
  simp only [CollatzResearch.WordTrace]
  refine ⟨101787853518513521927368973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67858569012342347951579315 101787853518513521927368973)
  ·
    refine ⟨38170445069442570722763365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101787853518513521927368973 38170445069442570722763365)
    ·
      refine ⟨7156958450520482010518131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38170445069442570722763365 7156958450520482010518131)
      ·
        refine ⟨10735437675780723015777197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7156958450520482010518131 10735437675780723015777197)
        ·
          refine ⟨4025789128417771130916449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10735437675780723015777197 4025789128417771130916449)
          ·
            refine ⟨3019341846313328348187337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025789128417771130916449 3019341846313328348187337)
            ·
              refine ⟨2264506384734996261140503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019341846313328348187337 2264506384734996261140503)
              ·
                refine ⟨3396759577102494391710755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264506384734996261140503 3396759577102494391710755)
                ·
                  refine ⟨5095139365653741587566133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396759577102494391710755 5095139365653741587566133)
                  ·
                    refine ⟨477669315530038273834325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5095139365653741587566133 477669315530038273834325)
                    ·
                      rfl

theorem cell23_2790773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2790773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790773 prefixEnd_2790773 := by exact prefixLift 2790773
  have htrace : WordTrace (prefixWord ++ tailWord_2790773) baseStart_2790773 baseEnd_2790773 := by
    simpa [prefixWord, tailWord_2790773, baseEnd_2790773] using wordTrace_append hprefix tailTrace_2790773
  have hstable : (prefixWord ++ tailWord_2790773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790773).length < 2 ^ (prefixWord ++ tailWord_2790773).sum := by decide
  have hdescent : baseEnd_2790773 < baseStart_2790773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790779 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 3]
def baseStart_2790779 : Nat := 118140960795 + 2790779 * 2 ^ 59
def prefixEnd_2790779 : Nat := 4983230072969 + 3 ^ 40 * 2790779 * 2
def baseEnd_2790779 : Nat := 1433011027474041798027947

theorem tailTrace_2790779 : CollatzResearch.WordTrace tailWord_2790779 prefixEnd_2790779 1433011027474041798027947 := by
  unfold tailWord_2790779
  simp only [CollatzResearch.WordTrace]
  refine ⟨101788072356491784952087391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67858714904327856634724927 101788072356491784952087391)
  ·
    refine ⟨152682108534737677428131087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101788072356491784952087391 152682108534737677428131087)
    ·
      refine ⟨229023162802106516142196631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152682108534737677428131087 229023162802106516142196631)
      ·
        refine ⟨343534744203159774213294947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229023162802106516142196631 343534744203159774213294947)
        ·
          refine ⟨515302116304739661319942421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343534744203159774213294947 515302116304739661319942421)
          ·
            refine ⟨24154786701784671624372301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 515302116304739661319942421 24154786701784671624372301)
            ·
              refine ⟨9058045013169251859139613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24154786701784671624372301 9058045013169251859139613)
              ·
                refine ⟨3396766879938469447177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9058045013169251859139613 3396766879938469447177355)
                ·
                  refine ⟨5095150319907704170766033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396766879938469447177355 5095150319907704170766033)
                  ·
                    refine ⟨3821362739930778128074525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5095150319907704170766033 3821362739930778128074525)
                    ·
                      refine ⟨1433011027474041798027947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821362739930778128074525 1433011027474041798027947)
                      ·
                        rfl

theorem cell23_2790779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 2, 3].length) (baseStart_2790779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790779 prefixEnd_2790779 := by exact prefixLift 2790779
  have htrace : WordTrace (prefixWord ++ tailWord_2790779) baseStart_2790779 baseEnd_2790779 := by
    simpa [prefixWord, tailWord_2790779, baseEnd_2790779] using wordTrace_append hprefix tailTrace_2790779
  have hstable : (prefixWord ++ tailWord_2790779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790779).length < 2 ^ (prefixWord ++ tailWord_2790779).sum := by decide
  have hdescent : baseEnd_2790779 < baseStart_2790779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790793 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 3, 2, 2]
def baseStart_2790793 : Nat := 118140960795 + 2790793 * 2 ^ 59
def prefixEnd_2790793 : Nat := 4983230072969 + 3 ^ 40 * 2790793 * 2
def baseEnd_2790793 : Nat := 1433018216203204743252883

theorem tailTrace_2790793 : CollatzResearch.WordTrace tailWord_2790793 prefixEnd_2790793 1433018216203204743252883 := by
  unfold tailWord_2790793
  simp only [CollatzResearch.WordTrace]
  refine ⟨101788582978441065343097033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67859055318960710228731355 101788582978441065343097033)
  ·
    refine ⟨76341437233830799007322775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101788582978441065343097033 76341437233830799007322775)
    ·
      refine ⟨114512155850746198510984163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76341437233830799007322775 114512155850746198510984163)
      ·
        refine ⟨171768233776119297766476245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114512155850746198510984163 171768233776119297766476245)
        ·
          refine ⟨4025817979127796041401787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 171768233776119297766476245 4025817979127796041401787)
          ·
            refine ⟨6038726968691694062102681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025817979127796041401787 6038726968691694062102681)
            ·
              refine ⟨4529045226518770546577011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038726968691694062102681 4529045226518770546577011)
              ·
                refine ⟨6793567839778155819865517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529045226518770546577011 6793567839778155819865517)
                ·
                  refine ⟨2547587939916808432449569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6793567839778155819865517 2547587939916808432449569)
                  ·
                    refine ⟨1910690954937606324337177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547587939916808432449569 1910690954937606324337177)
                    ·
                      refine ⟨1433018216203204743252883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910690954937606324337177 1433018216203204743252883)
                      ·
                        rfl

theorem cell23_2790793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 2, 2].length) (baseStart_2790793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790793 prefixEnd_2790793 := by exact prefixLift 2790793
  have htrace : WordTrace (prefixWord ++ tailWord_2790793) baseStart_2790793 baseEnd_2790793 := by
    simpa [prefixWord, tailWord_2790793, baseEnd_2790793] using wordTrace_append hprefix tailTrace_2790793
  have hstable : (prefixWord ++ tailWord_2790793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790793).length < 2 ^ (prefixWord ++ tailWord_2790793).sum := by decide
  have hdescent : baseEnd_2790793 < baseStart_2790793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790809 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2790809 : Nat := 118140960795 + 2790809 * 2 ^ 59
def prefixEnd_2790809 : Nat := 4983230072969 + 3 ^ 40 * 2790809 * 2
def baseEnd_2790809 : Nat := 1433026431893676680652809

theorem tailTrace_2790809 : CollatzResearch.WordTrace tailWord_2790809 prefixEnd_2790809 1433026431893676680652809 := by
  unfold tailWord_2790809
  simp only [CollatzResearch.WordTrace]
  refine ⟨101789166546383100075679481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67859444364255400050452987 101789166546383100075679481)
  ·
    refine ⟨76341874909787325056759611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101789166546383100075679481 76341874909787325056759611)
    ·
      refine ⟨114512812364680987585139417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76341874909787325056759611 114512812364680987585139417)
      ·
        refine ⟨85884609273510740688854563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114512812364680987585139417 85884609273510740688854563)
        ·
          refine ⟨128826913910266111033281845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85884609273510740688854563 128826913910266111033281845)
          ·
            refine ⟨12077523179087447909370173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128826913910266111033281845 12077523179087447909370173)
            ·
              refine ⟨4529071192157792966013815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12077523179087447909370173 4529071192157792966013815)
              ·
                refine ⟨6793606788236689449020723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529071192157792966013815 6793606788236689449020723)
                ·
                  refine ⟨10190410182355034173531085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793606788236689449020723 10190410182355034173531085)
                  ·
                    refine ⟨3821403818383137815074157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10190410182355034173531085 3821403818383137815074157)
                    ·
                      refine ⟨1433026431893676680652809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821403818383137815074157 1433026431893676680652809)
                      ·
                        rfl

theorem cell23_2790809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2790809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790809 prefixEnd_2790809 := by exact prefixLift 2790809
  have htrace : WordTrace (prefixWord ++ tailWord_2790809) baseStart_2790809 baseEnd_2790809 := by
    simpa [prefixWord, tailWord_2790809, baseEnd_2790809] using wordTrace_append hprefix tailTrace_2790809
  have hstable : (prefixWord ++ tailWord_2790809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790809).length < 2 ^ (prefixWord ++ tailWord_2790809).sum := by decide
  have hdescent : baseEnd_2790809 < baseStart_2790809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790850 : List Nat := [3, 5, 2, 1, 1, 1, 2, 8]
def baseStart_2790850 : Nat := 118140960795 + 2790850 * 2 ^ 59
def prefixEnd_2790850 : Nat := 4983230072969 + 3 ^ 40 * 2790850 * 2
def baseEnd_2790850 : Nat := 53075832762981889638523

theorem tailTrace_2790850 : CollatzResearch.WordTrace tailWord_2790850 prefixEnd_2790850 53075832762981889638523 := by
  unfold tailWord_2790850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447665484808641019480501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67860441292823042718614669 25447665484808641019480501)
  ·
    refine ⟨2385718639200810095576297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25447665484808641019480501 2385718639200810095576297)
    ·
      refine ⟨1789288979400607571682223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2385718639200810095576297 1789288979400607571682223)
      ·
        refine ⟨2683933469100911357523335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789288979400607571682223 2683933469100911357523335)
        ·
          refine ⟨4025900203651367036285003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683933469100911357523335 4025900203651367036285003)
          ·
            refine ⟨6038850305477050554427505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025900203651367036285003 6038850305477050554427505)
            ·
              refine ⟨4529137729107787915820629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038850305477050554427505 4529137729107787915820629)
              ·
                refine ⟨53075832762981889638523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4529137729107787915820629 53075832762981889638523)
                ·
                  rfl

theorem cell23_2790850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_2790850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790850 prefixEnd_2790850 := by exact prefixLift 2790850
  have htrace : WordTrace (prefixWord ++ tailWord_2790850) baseStart_2790850 baseEnd_2790850 := by
    simpa [prefixWord, tailWord_2790850, baseEnd_2790850] using wordTrace_append hprefix tailTrace_2790850
  have hstable : (prefixWord ++ tailWord_2790850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790850).length < 2 ^ (prefixWord ++ tailWord_2790850).sum := by decide
  have hdescent : baseEnd_2790850 < baseStart_2790850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790860 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2790860 : Nat := 118140960795 + 2790860 * 2 ^ 59
def prefixEnd_2790860 : Nat := 4983230072969 + 3 ^ 40 * 2790860 * 2
def baseEnd_2790860 : Nat := 1433052619407055981115075

theorem tailTrace_2790860 : CollatzResearch.WordTrace tailWord_2790860 prefixEnd_2790860 1433052619407055981115075 := by
  unfold tailWord_2790860
  simp only [CollatzResearch.WordTrace]
  refine ⟨50895513334599167892893017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67860684446132223857190689 50895513334599167892893017)
  ·
    refine ⟨38171635000949375919669763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50895513334599167892893017 38171635000949375919669763)
    ·
      refine ⟨57257452501424063879504645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38171635000949375919669763 57257452501424063879504645)
      ·
        refine ⟨10735772344017011977407121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57257452501424063879504645 10735772344017011977407121)
        ·
          refine ⟨8051829258012758983055341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10735772344017011977407121 8051829258012758983055341)
          ·
            refine ⟨3019435971754784618645753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8051829258012758983055341 3019435971754784618645753)
            ·
              refine ⟨2264576978816088463984315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019435971754784618645753 2264576978816088463984315)
              ·
                refine ⟨3396865468224132695976473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264576978816088463984315 3396865468224132695976473)
                ·
                  refine ⟨2547649101168099521982355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396865468224132695976473 2547649101168099521982355)
                  ·
                    refine ⟨3821473651752149282973533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547649101168099521982355 3821473651752149282973533)
                    ·
                      refine ⟨1433052619407055981115075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821473651752149282973533 1433052619407055981115075)
                      ·
                        rfl

theorem cell23_2790860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2790860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790860 prefixEnd_2790860 := by exact prefixLift 2790860
  have htrace : WordTrace (prefixWord ++ tailWord_2790860) baseStart_2790860 baseEnd_2790860 := by
    simpa [prefixWord, tailWord_2790860, baseEnd_2790860] using wordTrace_append hprefix tailTrace_2790860
  have hstable : (prefixWord ++ tailWord_2790860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790860).length < 2 ^ (prefixWord ++ tailWord_2790860).sum := by decide
  have hdescent : baseEnd_2790860 < baseStart_2790860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790870 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2790870 : Nat := 118140960795 + 2790870 * 2 ^ 59
def prefixEnd_2790870 : Nat := 4983230072969 + 3 ^ 40 * 2790870 * 2
def baseEnd_2790870 : Nat := 1433057754213600941990029

theorem tailTrace_2790870 : CollatzResearch.WordTrace tailWord_2790870 prefixEnd_2790870 1433057754213600941990029 := by
  unfold tailWord_2790870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6361961962447631718353129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67860927599441404995766709 6361961962447631718353129)
  ·
    refine ⟨4771471471835723788764847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6361961962447631718353129 4771471471835723788764847)
    ·
      refine ⟨7157207207753585683147271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771471471835723788764847 7157207207753585683147271)
      ·
        refine ⟨10735810811630378524720907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157207207753585683147271 10735810811630378524720907)
        ·
          refine ⟨16103716217445567787081361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735810811630378524720907 16103716217445567787081361)
          ·
            refine ⟨12077787163084175840311021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16103716217445567787081361 12077787163084175840311021)
            ·
              refine ⟨4529170186156565940116633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12077787163084175840311021 4529170186156565940116633)
              ·
                refine ⟨3396877639617424455087475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529170186156565940116633 3396877639617424455087475)
                ·
                  refine ⟨5095316459426136682631213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396877639617424455087475 5095316459426136682631213)
                  ·
                    refine ⟨1910743672284801255986705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5095316459426136682631213 1910743672284801255986705)
                    ·
                      refine ⟨1433057754213600941990029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910743672284801255986705 1433057754213600941990029)
                      ·
                        rfl

theorem cell23_2790870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2790870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790870 prefixEnd_2790870 := by exact prefixLift 2790870
  have htrace : WordTrace (prefixWord ++ tailWord_2790870) baseStart_2790870 baseEnd_2790870 := by
    simpa [prefixWord, tailWord_2790870, baseEnd_2790870] using wordTrace_append hprefix tailTrace_2790870
  have hstable : (prefixWord ++ tailWord_2790870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790870).length < 2 ^ (prefixWord ++ tailWord_2790870).sum := by decide
  have hdescent : baseEnd_2790870 < baseStart_2790870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790872 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 7]
def baseStart_2790872 : Nat := 118140960795 + 2790872 * 2 ^ 59
def prefixEnd_2790872 : Nat := 4983230072969 + 3 ^ 40 * 2790872 * 2
def baseEnd_2790872 : Nat := 159228753463878881573891

theorem tailTrace_2790872 : CollatzResearch.WordTrace tailWord_2790872 prefixEnd_2790872 159228753463878881573891 := by
  unfold tailWord_2790872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50895732172577430917611435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67860976230103241223481913 50895732172577430917611435)
  ·
    refine ⟨76343598258866146376417153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50895732172577430917611435 76343598258866146376417153)
    ·
      refine ⟨57257698694149609782312865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76343598258866146376417153 57257698694149609782312865)
      ·
        refine ⟨42943274020612207336734649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57257698694149609782312865 42943274020612207336734649)
        ·
          refine ⟨32207455515459155502550987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42943274020612207336734649 32207455515459155502550987)
          ·
            refine ⟨48311183273188733253826481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32207455515459155502550987 48311183273188733253826481)
            ·
              refine ⟨36233387454891549940369861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48311183273188733253826481 36233387454891549940369861)
              ·
                refine ⟨6793760147792165613819349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36233387454891549940369861 6793760147792165613819349)
                ·
                  refine ⟨159228753463878881573891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6793760147792165613819349 159228753463878881573891)
                  ·
                    rfl

theorem cell23_2790872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_2790872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790872 prefixEnd_2790872 := by exact prefixLift 2790872
  have htrace : WordTrace (prefixWord ++ tailWord_2790872) baseStart_2790872 baseEnd_2790872 := by
    simpa [prefixWord, tailWord_2790872, baseEnd_2790872] using wordTrace_append hprefix tailTrace_2790872
  have hstable : (prefixWord ++ tailWord_2790872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790872).length < 2 ^ (prefixWord ++ tailWord_2790872).sum := by decide
  have hdescent : baseEnd_2790872 < baseStart_2790872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2790949 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_2790949 : Nat := 118140960795 + 2790949 * 2 ^ 59
def prefixEnd_2790949 : Nat := 4983230072969 + 3 ^ 40 * 2790949 * 2
def baseEnd_2790949 : Nat := 477699439728435377634055

theorem tailTrace_2790949 : CollatzResearch.WordTrace tailWord_2790949 prefixEnd_2790949 477699439728435377634055 := by
  unfold tailWord_2790949
  simp only [CollatzResearch.WordTrace]
  refine ⟨101794272765875903985775901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67862848510583935990517267 101794272765875903985775901)
  ·
    refine ⟨38172852287203463994665963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101794272765875903985775901 38172852287203463994665963)
    ·
      refine ⟨57259278430805195991998945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38172852287203463994665963 57259278430805195991998945)
      ·
        refine ⟨42944458823103896993999209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57259278430805195991998945 42944458823103896993999209)
        ·
          refine ⟨32208344117327922745499407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42944458823103896993999209 32208344117327922745499407)
          ·
            refine ⟨48312516175991884118249111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32208344117327922745499407 48312516175991884118249111)
            ·
              refine ⟨72468774263987826177373667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48312516175991884118249111 72468774263987826177373667)
              ·
                refine ⟨108703161395981739266060501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72468774263987826177373667 108703161395981739266060501)
                ·
                  refine ⟨2547730345218322014048293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108703161395981739266060501 2547730345218322014048293)
                  ·
                    refine ⟨477699439728435377634055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547730345218322014048293 477699439728435377634055)
                    ·
                      rfl

theorem cell23_2790949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_2790949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2790949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2790949 prefixEnd_2790949 := by exact prefixLift 2790949
  have htrace : WordTrace (prefixWord ++ tailWord_2790949) baseStart_2790949 baseEnd_2790949 := by
    simpa [prefixWord, tailWord_2790949, baseEnd_2790949] using wordTrace_append hprefix tailTrace_2790949
  have hstable : (prefixWord ++ tailWord_2790949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2790949).length < 2 ^ (prefixWord ++ tailWord_2790949).sum := by decide
  have hdescent : baseEnd_2790949 < baseStart_2790949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2790949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791030 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2791030 : Nat := 118140960795 + 2791030 * 2 ^ 59
def prefixEnd_2791030 : Nat := 4983230072969 + 3 ^ 40 * 2791030 * 2
def baseEnd_2791030 : Nat := 159237767902035590665477

theorem tailTrace_2791030 : CollatzResearch.WordTrace tailWord_2791030 prefixEnd_2791030 159237767902035590665477 := by
  unfold tailWord_2791030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362326692411403426217159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67864818052388303212983029 6362326692411403426217159)
  ·
    refine ⟨9543490038617105139325739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6362326692411403426217159 9543490038617105139325739)
    ·
      refine ⟨14315235057925657708988609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543490038617105139325739 14315235057925657708988609)
      ·
        refine ⟨10736426293444243281741457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14315235057925657708988609 10736426293444243281741457)
        ·
          refine ⟨8052319720083182461306093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10736426293444243281741457 8052319720083182461306093)
          ·
            refine ⟨3019619895031193422989785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8052319720083182461306093 3019619895031193422989785)
            ·
              refine ⟨2264714921273395067242339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019619895031193422989785 2264714921273395067242339)
              ·
                refine ⟨3397072381910092600863509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264714921273395067242339 3397072381910092600863509)
                ·
                  refine ⟨159237767902035590665477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3397072381910092600863509 159237767902035590665477)
                  ·
                    rfl

theorem cell23_2791030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2791030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791030 prefixEnd_2791030 := by exact prefixLift 2791030
  have htrace : WordTrace (prefixWord ++ tailWord_2791030) baseStart_2791030 baseEnd_2791030 := by
    simpa [prefixWord, tailWord_2791030, baseEnd_2791030] using wordTrace_append hprefix tailTrace_2791030
  have hstable : (prefixWord ++ tailWord_2791030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791030).length < 2 ^ (prefixWord ++ tailWord_2791030).sum := by decide
  have hdescent : baseEnd_2791030 < baseStart_2791030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791049 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_2791049 : Nat := 118140960795 + 2791049 * 2 ^ 59
def prefixEnd_2791049 : Nat := 4983230072969 + 3 ^ 40 * 2791049 * 2
def baseEnd_2791049 : Nat := 1433149667250755741651705

theorem tailTrace_2791049 : CollatzResearch.WordTrace tailWord_2791049 prefixEnd_2791049 1433149667250755741651705 := by
  unfold tailWord_2791049
  simp only [CollatzResearch.WordTrace]
  refine ⟨101797920065513621064416201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67865280043675747376277467 101797920065513621064416201)
  ·
    refine ⟨76348440049135215798312151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101797920065513621064416201 76348440049135215798312151)
    ·
      refine ⟨114522660073702823697468227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76348440049135215798312151 114522660073702823697468227)
      ·
        refine ⟨171783990110554235546202341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114522660073702823697468227 171783990110554235546202341)
        ·
          refine ⟨32209498145728919164912939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171783990110554235546202341 32209498145728919164912939)
          ·
            refine ⟨48314247218593378747369409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32209498145728919164912939 48314247218593378747369409)
            ·
              refine ⟨36235685413945034060527057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48314247218593378747369409 36235685413945034060527057)
              ·
                refine ⟨27176764060458775545395293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36235685413945034060527057 27176764060458775545395293)
                ·
                  refine ⟨10191286522672040829523235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27176764060458775545395293 10191286522672040829523235)
                  ·
                    refine ⟨15286929784008061244284853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10191286522672040829523235 15286929784008061244284853)
                    ·
                      refine ⟨1433149667250755741651705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15286929784008061244284853 1433149667250755741651705)
                      ·
                        rfl

theorem cell23_2791049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_2791049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791049 prefixEnd_2791049 := by exact prefixLift 2791049
  have htrace : WordTrace (prefixWord ++ tailWord_2791049) baseStart_2791049 baseEnd_2791049 := by
    simpa [prefixWord, tailWord_2791049, baseEnd_2791049] using wordTrace_append hprefix tailTrace_2791049
  have hstable : (prefixWord ++ tailWord_2791049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791049).length < 2 ^ (prefixWord ++ tailWord_2791049).sum := by decide
  have hdescent : baseEnd_2791049 < baseStart_2791049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791050 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_2791050 : Nat := 118140960795 + 2791050 * 2 ^ 59
def prefixEnd_2791050 : Nat := 4983230072969 + 3 ^ 40 * 2791050 * 2
def baseEnd_2791050 : Nat := 1433150180731410237739201

theorem tailTrace_2791050 : CollatzResearch.WordTrace tailWord_2791050 prefixEnd_2791050 1433150180731410237739201 := by
  unfold tailWord_2791050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25449489134627499558800651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67865304359006665490135069 25449489134627499558800651)
  ·
    refine ⟨38174233701941249338200977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25449489134627499558800651 38174233701941249338200977)
    ·
      refine ⟨28630675276455937003650733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38174233701941249338200977 28630675276455937003650733)
      ·
        refine ⟨10736503228670976376369025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28630675276455937003650733 10736503228670976376369025)
        ·
          refine ⟨8052377421503232282276769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10736503228670976376369025 8052377421503232282276769)
          ·
            refine ⟨6039283066127424211707577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052377421503232282276769 6039283066127424211707577)
            ·
              refine ⟨4529462299595568158780683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6039283066127424211707577 4529462299595568158780683)
              ·
                refine ⟨6794193449393352238171025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529462299595568158780683 6794193449393352238171025)
                ·
                  refine ⟨5095645087045014178628269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794193449393352238171025 5095645087045014178628269)
                  ·
                    refine ⟨1910866907641880316985601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5095645087045014178628269 1910866907641880316985601)
                    ·
                      refine ⟨1433150180731410237739201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910866907641880316985601 1433150180731410237739201)
                      ·
                        rfl

theorem cell23_2791050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_2791050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791050 prefixEnd_2791050 := by exact prefixLift 2791050
  have htrace : WordTrace (prefixWord ++ tailWord_2791050) baseStart_2791050 baseEnd_2791050 := by
    simpa [prefixWord, tailWord_2791050, baseEnd_2791050] using wordTrace_append hprefix tailTrace_2791050
  have hstable : (prefixWord ++ tailWord_2791050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791050).length < 2 ^ (prefixWord ++ tailWord_2791050).sum := by decide
  have hdescent : baseEnd_2791050 < baseStart_2791050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791073 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2791073 : Nat := 118140960795 + 2791073 * 2 ^ 59
def prefixEnd_2791073 : Nat := 4983230072969 + 3 ^ 40 * 2791073 * 2
def baseEnd_2791073 : Nat := 477720663595487882583865

theorem tailTrace_2791073 : CollatzResearch.WordTrace tailWord_2791073 prefixEnd_2791073 477720663595487882583865 := by
  unfold tailWord_2791073
  simp only [CollatzResearch.WordTrace]
  refine ⟨101798795417426673163289873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67865863611617782108859915 101798795417426673163289873)
  ·
    refine ⟨76349096563070004872467405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101798795417426673163289873 76349096563070004872467405)
    ·
      refine ⟨28630911211151251827175277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76349096563070004872467405 28630911211151251827175277)
      ·
        refine ⟨10736591704181719435190729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28630911211151251827175277 10736591704181719435190729)
        ·
          refine ⟨8052443778136289576393047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10736591704181719435190729 8052443778136289576393047)
          ·
            refine ⟨12078665667204434364589571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052443778136289576393047 12078665667204434364589571)
            ·
              refine ⟨18117998500806651546884357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078665667204434364589571 18117998500806651546884357)
              ·
                refine ⟨3397124718901247165040817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18117998500806651546884357 3397124718901247165040817)
                ·
                  refine ⟨2547843539175935373780613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397124718901247165040817 2547843539175935373780613)
                  ·
                    refine ⟨477720663595487882583865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547843539175935373780613 477720663595487882583865)
                    ·
                      rfl

theorem cell23_2791073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2791073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791073 prefixEnd_2791073 := by exact prefixLift 2791073
  have htrace : WordTrace (prefixWord ++ tailWord_2791073) baseStart_2791073 baseEnd_2791073 := by
    simpa [prefixWord, tailWord_2791073, baseEnd_2791073] using wordTrace_append hprefix tailTrace_2791073
  have hstable : (prefixWord ++ tailWord_2791073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791073).length < 2 ^ (prefixWord ++ tailWord_2791073).sum := by decide
  have hdescent : baseEnd_2791073 < baseStart_2791073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791074 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2791074 : Nat := 118140960795 + 2791074 * 2 ^ 59
def prefixEnd_2791074 : Nat := 4983230072969 + 3 ^ 40 * 2791074 * 2
def baseEnd_2791074 : Nat := 1433162504267118143839091

theorem tailTrace_2791074 : CollatzResearch.WordTrace tailWord_2791074 prefixEnd_2791074 1433162504267118143839091 := by
  unfold tailWord_2791074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25449707972605762583519069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67865887926948700222717517 25449707972605762583519069)
  ·
    refine ⟨9543640489727160968819651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25449707972605762583519069 9543640489727160968819651)
    ·
      refine ⟨14315460734590741453229477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543640489727160968819651 14315460734590741453229477)
      ·
        refine ⟨2684148887735764022480527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14315460734590741453229477 2684148887735764022480527)
        ·
          refine ⟨4026223331603646033720791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684148887735764022480527 4026223331603646033720791)
          ·
            refine ⟨6039334997405469050581187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026223331603646033720791 6039334997405469050581187)
            ·
              refine ⟨9059002496108203575871781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039334997405469050581187 9059002496108203575871781)
              ·
                refine ⟨1698562968020288170475959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9059002496108203575871781 1698562968020288170475959)
                ·
                  refine ⟨2547844452030432255713939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698562968020288170475959 2547844452030432255713939)
                  ·
                    refine ⟨3821766678045648383570909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547844452030432255713939 3821766678045648383570909)
                    ·
                      refine ⟨1433162504267118143839091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821766678045648383570909 1433162504267118143839091)
                      ·
                        rfl

theorem cell23_2791074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2791074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791074 prefixEnd_2791074 := by exact prefixLift 2791074
  have htrace : WordTrace (prefixWord ++ tailWord_2791074) baseStart_2791074 baseEnd_2791074 := by
    simpa [prefixWord, tailWord_2791074, baseEnd_2791074] using wordTrace_append hprefix tailTrace_2791074
  have hstable : (prefixWord ++ tailWord_2791074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791074).length < 2 ^ (prefixWord ++ tailWord_2791074).sum := by decide
  have hdescent : baseEnd_2791074 < baseStart_2791074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791109 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_2791109 : Nat := 118140960795 + 2791109 * 2 ^ 59
def prefixEnd_2791109 : Nat := 4983230072969 + 3 ^ 40 * 2791109 * 2
def baseEnd_2791109 : Nat := 1433180476090025506901429

theorem tailTrace_2791109 : CollatzResearch.WordTrace tailWord_2791109 prefixEnd_2791109 1433180476090025506901429 := by
  unfold tailWord_2791109
  simp only [CollatzResearch.WordTrace]
  refine ⟨101800108445296251311600381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67866738963530834207733587 101800108445296251311600381)
  ·
    refine ⟨38175040666986094241850143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101800108445296251311600381 38175040666986094241850143)
    ·
      refine ⟨57262561000479141362775215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38175040666986094241850143 57262561000479141362775215)
      ·
        refine ⟨85893841500718712044162823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57262561000479141362775215 85893841500718712044162823)
        ·
          refine ⟨128840762251078068066244235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85893841500718712044162823 128840762251078068066244235)
          ·
            refine ⟨193261143376617102099366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128840762251078068066244235 193261143376617102099366353)
            ·
              refine ⟨144945857532462826574524765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193261143376617102099366353 144945857532462826574524765)
              ·
                refine ⟨54354696574673559965446787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144945857532462826574524765 54354696574673559965446787)
                ·
                  refine ⟨81532044862010339948170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54354696574673559965446787 81532044862010339948170181)
                  ·
                    refine ⟨15287258411626938740281909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81532044862010339948170181 15287258411626938740281909)
                    ·
                      refine ⟨1433180476090025506901429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15287258411626938740281909 1433180476090025506901429)
                      ·
                        rfl

theorem cell23_2791109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_2791109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791109 prefixEnd_2791109 := by exact prefixLift 2791109
  have htrace : WordTrace (prefixWord ++ tailWord_2791109) baseStart_2791109 baseEnd_2791109 := by
    simpa [prefixWord, tailWord_2791109, baseEnd_2791109] using wordTrace_append hprefix tailTrace_2791109
  have hstable : (prefixWord ++ tailWord_2791109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791109).length < 2 ^ (prefixWord ++ tailWord_2791109).sum := by decide
  have hdescent : baseEnd_2791109 < baseStart_2791109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791114 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_2791114 : Nat := 118140960795 + 2791114 * 2 ^ 59
def prefixEnd_2791114 : Nat := 4983230072969 + 3 ^ 40 * 2791114 * 2
def baseEnd_2791114 : Nat := 1433183043493297987338907

theorem tailTrace_2791114 : CollatzResearch.WordTrace tailWord_2791114 prefixEnd_2791114 1433183043493297987338907 := by
  unfold tailWord_2791114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450072702569534291383099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67866860540185424777021597 25450072702569534291383099)
  ·
    refine ⟨38175109053854301437074649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25450072702569534291383099 38175109053854301437074649)
    ·
      refine ⟨28631331790390726077805987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38175109053854301437074649 28631331790390726077805987)
      ·
        refine ⟨42946997685586089116708981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28631331790390726077805987 42946997685586089116708981)
        ·
          refine ⟨4026281033023695854691467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42946997685586089116708981 4026281033023695854691467)
          ·
            refine ⟨6039421549535543782037201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026281033023695854691467 6039421549535543782037201)
            ·
              refine ⟨4529566162151657836527901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6039421549535543782037201 4529566162151657836527901)
              ·
                refine ⟨1698587310806871688697963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4529566162151657836527901 1698587310806871688697963)
                ·
                  refine ⟨2547880966210307533046945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698587310806871688697963 2547880966210307533046945)
                  ·
                    refine ⟨1910910724657730649785209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547880966210307533046945 1910910724657730649785209)
                    ·
                      refine ⟨1433183043493297987338907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910910724657730649785209 1433183043493297987338907)
                      ·
                        rfl

theorem cell23_2791114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_2791114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791114 prefixEnd_2791114 := by exact prefixLift 2791114
  have htrace : WordTrace (prefixWord ++ tailWord_2791114) baseStart_2791114 baseEnd_2791114 := by
    simpa [prefixWord, tailWord_2791114, baseEnd_2791114] using wordTrace_append hprefix tailTrace_2791114
  have hstable : (prefixWord ++ tailWord_2791114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791114).length < 2 ^ (prefixWord ++ tailWord_2791114).sum := by decide
  have hdescent : baseEnd_2791114 < baseStart_2791114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791117 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2791117 : Nat := 118140960795 + 2791117 * 2 ^ 59
def prefixEnd_2791117 : Nat := 4983230072969 + 3 ^ 40 * 2791117 * 2
def baseEnd_2791117 : Nat := 1433184583935261475601393

theorem tailTrace_2791117 : CollatzResearch.WordTrace tailWord_2791117 prefixEnd_2791117 1433184583935261475601393 := by
  unfold tailWord_2791117
  simp only [CollatzResearch.WordTrace]
  refine ⟨101800400229267268677891605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67866933486178179118594403 101800400229267268677891605)
  ·
    refine ⟨4771893760746903219276169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101800400229267268677891605 4771893760746903219276169)
    ·
      refine ⟨3578920320560177414457127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4771893760746903219276169 3578920320560177414457127)
      ·
        refine ⟨5368380480840266121685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578920320560177414457127 5368380480840266121685691)
        ·
          refine ⟨8052570721260399182528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368380480840266121685691 8052570721260399182528537)
          ·
            refine ⟨6039428040945299386896403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8052570721260399182528537 6039428040945299386896403)
            ·
              refine ⟨9059142061417949080344605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039428040945299386896403 9059142061417949080344605)
              ·
                refine ⟨3397178273031730905129227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9059142061417949080344605 3397178273031730905129227)
                ·
                  refine ⟨5095767409547596357693841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397178273031730905129227 5095767409547596357693841)
                  ·
                    refine ⟨3821825557160697268270381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5095767409547596357693841 3821825557160697268270381)
                    ·
                      refine ⟨1433184583935261475601393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821825557160697268270381 1433184583935261475601393)
                      ·
                        rfl

theorem cell23_2791117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2791117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791117 prefixEnd_2791117 := by exact prefixLift 2791117
  have htrace : WordTrace (prefixWord ++ tailWord_2791117) baseStart_2791117 baseEnd_2791117 := by
    simpa [prefixWord, tailWord_2791117, baseEnd_2791117] using wordTrace_append hprefix tailTrace_2791117
  have hstable : (prefixWord ++ tailWord_2791117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791117).length < 2 ^ (prefixWord ++ tailWord_2791117).sum := by decide
  have hdescent : baseEnd_2791117 < baseStart_2791117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791130 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_2791130 : Nat := 118140960795 + 2791130 * 2 ^ 59
def prefixEnd_2791130 : Nat := 4983230072969 + 3 ^ 40 * 2791130 * 2
def baseEnd_2791130 : Nat := 1433191259183769924738833

theorem tailTrace_2791130 : CollatzResearch.WordTrace tailWord_2791130 prefixEnd_2791130 1433191259183769924738833 := by
  unfold tailWord_2791130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450218594555042974528711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67867249585480114598743229 25450218594555042974528711)
  ·
    refine ⟨38175327891832564461793067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25450218594555042974528711 38175327891832564461793067)
    ·
      refine ⟨57262991837748846692689601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38175327891832564461793067 57262991837748846692689601)
      ·
        refine ⟨42947243878311635019517201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57262991837748846692689601 42947243878311635019517201)
        ·
          refine ⟨32210432908733726264637901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42947243878311635019517201 32210432908733726264637901)
          ·
            refine ⟨12078912340775147349239213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32210432908733726264637901 12078912340775147349239213)
            ·
              refine ⟨4529592127790680255964705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12078912340775147349239213 4529592127790680255964705)
              ·
                refine ⟨3397194095843010191973529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529592127790680255964705 3397194095843010191973529)
                ·
                  refine ⟨2547895571882257643980147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397194095843010191973529 2547895571882257643980147)
                  ·
                    refine ⟨3821843357823386465970221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547895571882257643980147 3821843357823386465970221)
                    ·
                      refine ⟨1433191259183769924738833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821843357823386465970221 1433191259183769924738833)
                      ·
                        rfl

theorem cell23_2791130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_2791130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791130 prefixEnd_2791130 := by exact prefixLift 2791130
  have htrace : WordTrace (prefixWord ++ tailWord_2791130) baseStart_2791130 baseEnd_2791130 := by
    simpa [prefixWord, tailWord_2791130, baseEnd_2791130] using wordTrace_append hprefix tailTrace_2791130
  have hstable : (prefixWord ++ tailWord_2791130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791130).length < 2 ^ (prefixWord ++ tailWord_2791130).sum := by decide
  have hdescent : baseEnd_2791130 < baseStart_2791130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791146 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_2791146 : Nat := 118140960795 + 2791146 * 2 ^ 59
def prefixEnd_2791146 : Nat := 4983230072969 + 3 ^ 40 * 2791146 * 2
def baseEnd_2791146 : Nat := 477733158291413954046253

theorem tailTrace_2791146 : CollatzResearch.WordTrace tailWord_2791146 prefixEnd_2791146 477733158291413954046253 := by
  unfold tailWord_2791146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450364486540551657674323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67867638630774804420464861 25450364486540551657674323)
  ·
    refine ⟨38175546729810827486511485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25450364486540551657674323 38175546729810827486511485)
    ·
      refine ⟨14315830023679060307441807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38175546729810827486511485 14315830023679060307441807)
      ·
        refine ⟨21473745035518590461162711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14315830023679060307441807 21473745035518590461162711)
        ·
          refine ⟨32210617553277885691744067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21473745035518590461162711 32210617553277885691744067)
          ·
            refine ⟨48315926329916828537616101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32210617553277885691744067 48315926329916828537616101)
            ·
              refine ⟨9059236186859405350803019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48315926329916828537616101 9059236186859405350803019)
              ·
                refine ⟨13588854280289108026204529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059236186859405350803019 13588854280289108026204529)
                ·
                  refine ⟨10191640710216831019653397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13588854280289108026204529 10191640710216831019653397)
                  ·
                    refine ⟨477733158291413954046253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10191640710216831019653397 477733158291413954046253)
                    ·
                      rfl

theorem cell23_2791146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_2791146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791146 prefixEnd_2791146 := by exact prefixLift 2791146
  have htrace : WordTrace (prefixWord ++ tailWord_2791146) baseStart_2791146 baseEnd_2791146 := by
    simpa [prefixWord, tailWord_2791146, baseEnd_2791146] using wordTrace_append hprefix tailTrace_2791146
  have hstable : (prefixWord ++ tailWord_2791146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791146).length < 2 ^ (prefixWord ++ tailWord_2791146).sum := by decide
  have hdescent : baseEnd_2791146 < baseStart_2791146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791170 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_2791170 : Nat := 118140960795 + 2791170 * 2 ^ 59
def prefixEnd_2791170 : Nat := 4983230072969 + 3 ^ 40 * 2791170 * 2
def baseEnd_2791170 : Nat := 1433211798409949768238649

theorem tailTrace_2791170 : CollatzResearch.WordTrace tailWord_2791170 prefixEnd_2791170 1433211798409949768238649 := by
  unfold tailWord_2791170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450583324518814682392741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67868222198716839153047309 25450583324518814682392741)
  ·
    refine ⟨4771984373347277752948639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25450583324518814682392741 4771984373347277752948639)
    ·
      refine ⟨7157976560020916629422959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771984373347277752948639 7157976560020916629422959)
      ·
        refine ⟨10736964840031374944134439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157976560020916629422959 10736964840031374944134439)
        ·
          refine ⟨16105447260047062416201659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10736964840031374944134439 16105447260047062416201659)
          ·
            refine ⟨24158170890070593624302489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16105447260047062416201659 24158170890070593624302489)
            ·
              refine ⟨18118628167552945218226867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24158170890070593624302489 18118628167552945218226867)
              ·
                refine ⟨27177942251329417827340301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118628167552945218226867 27177942251329417827340301)
                ·
                  refine ⟨10191728344248531685252613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27177942251329417827340301 10191728344248531685252613)
                  ·
                    refine ⟨1910949064546599690984865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10191728344248531685252613 1910949064546599690984865)
                    ·
                      refine ⟨1433211798409949768238649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910949064546599690984865 1433211798409949768238649)
                      ·
                        rfl

theorem cell23_2791170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_2791170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791170 prefixEnd_2791170 := by exact prefixLift 2791170
  have htrace : WordTrace (prefixWord ++ tailWord_2791170) baseStart_2791170 baseEnd_2791170 := by
    simpa [prefixWord, tailWord_2791170, baseEnd_2791170] using wordTrace_append hprefix tailTrace_2791170
  have hstable : (prefixWord ++ tailWord_2791170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791170).length < 2 ^ (prefixWord ++ tailWord_2791170).sum := by decide
  have hdescent : baseEnd_2791170 < baseStart_2791170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791198 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2791198 : Nat := 118140960795 + 2791198 * 2 ^ 59
def prefixEnd_2791198 : Nat := 4983230072969 + 3 ^ 40 * 2791198 * 2
def baseEnd_2791198 : Nat := 1433226175868275658688521

theorem tailTrace_2791198 : CollatzResearch.WordTrace tailWord_2791198 prefixEnd_2791198 1433226175868275658688521 := by
  unfold tailWord_2791198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725419317746727438948781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67868903027982546341060165 12725419317746727438948781)
  ·
    refine ⟨4772032244155022789605793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12725419317746727438948781 4772032244155022789605793)
    ·
      refine ⟨3579024183116267092204345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4772032244155022789605793 3579024183116267092204345)
      ·
        refine ⟨2684268137337200319153259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3579024183116267092204345 2684268137337200319153259)
        ·
          refine ⟨4026402206005800478729889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684268137337200319153259 4026402206005800478729889)
          ·
            refine ⟨3019801654504350359047417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4026402206005800478729889 3019801654504350359047417)
            ·
              refine ⟨2264851240878262769285563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019801654504350359047417 2264851240878262769285563)
              ·
                refine ⟨3397276861317394153928345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264851240878262769285563 3397276861317394153928345)
                ·
                  refine ⟨2547957645988045615446259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397276861317394153928345 2547957645988045615446259)
                  ·
                    refine ⟨3821936468982068423169389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547957645988045615446259 3821936468982068423169389)
                    ·
                      refine ⟨1433226175868275658688521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3821936468982068423169389 1433226175868275658688521)
                      ·
                        rfl

theorem cell23_2791198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2791198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791198 prefixEnd_2791198 := by exact prefixLift 2791198
  have htrace : WordTrace (prefixWord ++ tailWord_2791198) baseStart_2791198 baseEnd_2791198 := by
    simpa [prefixWord, tailWord_2791198, baseEnd_2791198] using wordTrace_append hprefix tailTrace_2791198
  have hstable : (prefixWord ++ tailWord_2791198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791198).length < 2 ^ (prefixWord ++ tailWord_2791198).sum := by decide
  have hdescent : baseEnd_2791198 < baseStart_2791198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791204 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_2791204 : Nat := 118140960795 + 2791204 * 2 ^ 59
def prefixEnd_2791204 : Nat := 4983230072969 + 3 ^ 40 * 2791204 * 2
def baseEnd_2791204 : Nat := 1433229256752202635213493

theorem tailTrace_2791204 : CollatzResearch.WordTrace tailWord_2791204 prefixEnd_2791204 1433229256752202635213493 := by
  unfold tailWord_2791204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50901786689976041268154333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67869048919968055024205777 50901786689976041268154333)
  ·
    refine ⟨19088170008741015475557875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50901786689976041268154333 19088170008741015475557875)
    ·
      refine ⟨28632255013111523213336813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19088170008741015475557875 28632255013111523213336813)
      ·
        refine ⟨10737095629916821205001305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28632255013111523213336813 10737095629916821205001305)
        ·
          refine ⟨8052821722437615903750979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10737095629916821205001305 8052821722437615903750979)
          ·
            refine ⟨12079232583656423855626469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052821722437615903750979 12079232583656423855626469)
            ·
              refine ⟨2264856109435579472929963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12079232583656423855626469 2264856109435579472929963)
              ·
                refine ⟨3397284164153369209394945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264856109435579472929963 3397284164153369209394945)
                ·
                  refine ⟨2547963123115026907046209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397284164153369209394945 2547963123115026907046209)
                  ·
                    refine ⟨1910972342336270180284657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2547963123115026907046209 1910972342336270180284657)
                    ·
                      refine ⟨1433229256752202635213493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1910972342336270180284657 1433229256752202635213493)
                      ·
                        rfl

theorem cell23_2791204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_2791204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791204 prefixEnd_2791204 := by exact prefixLift 2791204
  have htrace : WordTrace (prefixWord ++ tailWord_2791204) baseStart_2791204 baseEnd_2791204 := by
    simpa [prefixWord, tailWord_2791204, baseEnd_2791204] using wordTrace_append hprefix tailTrace_2791204
  have hstable : (prefixWord ++ tailWord_2791204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791204).length < 2 ^ (prefixWord ++ tailWord_2791204).sum := by decide
  have hdescent : baseEnd_2791204 < baseStart_2791204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791244 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 5]
def baseStart_2791244 : Nat := 118140960795 + 2791244 * 2 ^ 59
def prefixEnd_2791244 : Nat := 4983230072969 + 3 ^ 40 * 2791244 * 2
def baseEnd_2791244 : Nat := 159249977330931386523701

theorem tailTrace_2791244 : CollatzResearch.WordTrace tailWord_2791244 prefixEnd_2791244 159249977330931386523701 := by
  unfold tailWord_2791244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50902516149903584683882393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67870021533204779578509857 50902516149903584683882393)
  ·
    refine ⟨38176887112427688512911795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50902516149903584683882393 38176887112427688512911795)
    ·
      refine ⟨57265330668641532769367693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38176887112427688512911795 57265330668641532769367693)
      ·
        refine ⟨21474499000740574788512885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57265330668641532769367693 21474499000740574788512885)
        ·
          refine ⟨2013234281319428886423083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21474499000740574788512885 2013234281319428886423083)
          ·
            refine ⟨3019851421979143329634625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013234281319428886423083 3019851421979143329634625)
            ·
              refine ⟨2264888566484357497225969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019851421979143329634625 2264888566484357497225969)
              ·
                refine ⟨1698666424863268122919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264888566484357497225969 1698666424863268122919477)
                ·
                  refine ⟨159249977330931386523701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698666424863268122919477 159249977330931386523701)
                  ·
                    rfl

theorem cell23_2791244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_2791244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791244 prefixEnd_2791244 := by exact prefixLift 2791244
  have htrace : WordTrace (prefixWord ++ tailWord_2791244) baseStart_2791244 baseEnd_2791244 := by
    simpa [prefixWord, tailWord_2791244, baseEnd_2791244] using wordTrace_append hprefix tailTrace_2791244
  have hstable : (prefixWord ++ tailWord_2791244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791244).length < 2 ^ (prefixWord ++ tailWord_2791244).sum := by decide
  have hdescent : baseEnd_2791244 < baseStart_2791244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791256 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2791256 : Nat := 118140960795 + 2791256 * 2 ^ 59
def prefixEnd_2791256 : Nat := 4983230072969 + 3 ^ 40 * 2791256 * 2
def baseEnd_2791256 : Nat := 1433255957746236431763253

theorem tailTrace_2791256 : CollatzResearch.WordTrace tailWord_2791256 prefixEnd_2791256 1433255957746236431763253 := by
  unfold tailWord_2791256
  simp only [CollatzResearch.WordTrace]
  refine ⟨50902734987881847708600811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67870313317175796944801081 50902734987881847708600811)
  ·
    refine ⟨76354102481822771562901217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50902734987881847708600811 76354102481822771562901217)
    ·
      refine ⟨57265576861367078672175913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76354102481822771562901217 57265576861367078672175913)
      ·
        refine ⟨42949182646025309004131935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57265576861367078672175913 42949182646025309004131935)
        ·
          refine ⟨64423773969037963506197903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42949182646025309004131935 64423773969037963506197903)
          ·
            refine ⟨96635660953556945259296855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64423773969037963506197903 96635660953556945259296855)
            ·
              refine ⟨144953491430335417888945283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96635660953556945259296855 144953491430335417888945283)
              ·
                refine ⟨217430237145503126833417925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144953491430335417888945283 217430237145503126833417925)
                ·
                  refine ⟨40768169464781836281265861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217430237145503126833417925 40768169464781836281265861)
                  ·
                    refine ⟨7644031774646594302737349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40768169464781836281265861 7644031774646594302737349)
                    ·
                      refine ⟨1433255957746236431763253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7644031774646594302737349 1433255957746236431763253)
                      ·
                        rfl

theorem cell23_2791256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2791256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791256 prefixEnd_2791256 := by exact prefixLift 2791256
  have htrace : WordTrace (prefixWord ++ tailWord_2791256) baseStart_2791256 baseEnd_2791256 := by
    simpa [prefixWord, tailWord_2791256, baseEnd_2791256] using wordTrace_append hprefix tailTrace_2791256
  have hstable : (prefixWord ++ tailWord_2791256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791256).length < 2 ^ (prefixWord ++ tailWord_2791256).sum := by decide
  have hdescent : baseEnd_2791256 < baseStart_2791256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791274 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2791274 : Nat := 118140960795 + 2791274 * 2 ^ 59
def prefixEnd_2791274 : Nat := 4983230072969 + 3 ^ 40 * 2791274 * 2
def baseEnd_2791274 : Nat := 477755066799339120446057

theorem tailTrace_2791274 : CollatzResearch.WordTrace tailWord_2791274 prefixEnd_2791274 477755066799339120446057 := by
  unfold tailWord_2791274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25451531622424621122839219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67870750993132322994237917 25451531622424621122839219)
  ·
    refine ⟨38177297433636931684258829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25451531622424621122839219 38177297433636931684258829)
    ·
      refine ⟨14316486537613849381597061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38177297433636931684258829 14316486537613849381597061)
      ·
        refine ⟨2684341225802596759049449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14316486537613849381597061 2684341225802596759049449)
        ·
          refine ⟨2013255919351947569287087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2684341225802596759049449 2013255919351947569287087)
          ·
            refine ⟨3019883879027921353930631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013255919351947569287087 3019883879027921353930631)
            ·
              refine ⟨4529825818541882030895947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019883879027921353930631 4529825818541882030895947)
              ·
                refine ⟨6794738727812823046343921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529825818541882030895947 6794738727812823046343921)
                ·
                  refine ⟨5096054045859617284757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6794738727812823046343921 5096054045859617284757941)
                  ·
                    refine ⟨477755066799339120446057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5096054045859617284757941 477755066799339120446057)
                    ·
                      rfl

theorem cell23_2791274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2791274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791274 prefixEnd_2791274 := by exact prefixLift 2791274
  have htrace : WordTrace (prefixWord ++ tailWord_2791274) baseStart_2791274 baseEnd_2791274 := by
    simpa [prefixWord, tailWord_2791274, baseEnd_2791274] using wordTrace_append hprefix tailTrace_2791274
  have hstable : (prefixWord ++ tailWord_2791274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791274).length < 2 ^ (prefixWord ++ tailWord_2791274).sum := by decide
  have hdescent : baseEnd_2791274 < baseStart_2791274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791333 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_2791333 : Nat := 118140960795 + 2791333 * 2 ^ 59
def prefixEnd_2791333 : Nat := 4983230072969 + 3 ^ 40 * 2791333 * 2
def baseEnd_2791333 : Nat := 1433295495756632630500399

theorem tailTrace_2791333 : CollatzResearch.WordTrace tailWord_2791333 prefixEnd_2791333 1433295495756632630500399 := by
  unfold tailWord_2791333
  simp only [CollatzResearch.WordTrace]
  refine ⟨101808278396484737567754653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67872185597656491711836435 101808278396484737567754653)
  ·
    refine ⟨38178104398681776587907995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101808278396484737567754653 38178104398681776587907995)
    ·
      refine ⟨57267156598022664881861993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38178104398681776587907995 57267156598022664881861993)
      ·
        refine ⟨42950367448516998661396495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57267156598022664881861993 42950367448516998661396495)
        ·
          refine ⟨64425551172775497992094743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42950367448516998661396495 64425551172775497992094743)
          ·
            refine ⟨96638326759163246988142115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64425551172775497992094743 96638326759163246988142115)
            ·
              refine ⟨144957490138744870482213173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96638326759163246988142115 144957490138744870482213173)
              ·
                refine ⟨13589764700507331607707485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144957490138744870482213173 13589764700507331607707485)
                ·
                  refine ⟨5096161762690249352890307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13589764700507331607707485 5096161762690249352890307)
                  ·
                    refine ⟨7644242644035374029335461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5096161762690249352890307 7644242644035374029335461)
                    ·
                      refine ⟨1433295495756632630500399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7644242644035374029335461 1433295495756632630500399)
                      ·
                        rfl

theorem cell23_2791333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_2791333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791333 prefixEnd_2791333 := by exact prefixLift 2791333
  have htrace : WordTrace (prefixWord ++ tailWord_2791333) baseStart_2791333 baseEnd_2791333 := by
    simpa [prefixWord, tailWord_2791333, baseEnd_2791333] using wordTrace_append hprefix tailTrace_2791333
  have hstable : (prefixWord ++ tailWord_2791333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791333).length < 2 ^ (prefixWord ++ tailWord_2791333).sum := by decide
  have hdescent : baseEnd_2791333 < baseStart_2791333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791343 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 6, 4]
def baseStart_2791343 : Nat := 118140960795 + 2791343 * 2 ^ 59
def prefixEnd_2791343 : Nat := 4983230072969 + 3 ^ 40 * 2791343 * 2
def baseEnd_2791343 : Nat := 477766876854392530458451

theorem tailTrace_2791343 : CollatzResearch.WordTrace tailWord_2791343 prefixEnd_2791343 477766876854392530458451 := by
  unfold tailWord_2791343
  simp only [CollatzResearch.WordTrace]
  refine ⟨101808643126448509275618683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67872428750965672850412455 101808643126448509275618683)
  ·
    refine ⟨152712964689672763913428025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101808643126448509275618683 152712964689672763913428025)
    ·
      refine ⟨114534723517254572935071019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152712964689672763913428025 114534723517254572935071019)
      ·
        refine ⟨171802085275881859402606529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114534723517254572935071019 171802085275881859402606529)
        ·
          refine ⟨128851563956911394551954897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171802085275881859402606529 128851563956911394551954897)
          ·
            refine ⟨96638672967683545913966173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128851563956911394551954897 96638672967683545913966173)
            ·
              refine ⟨36239502362881329717737315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96638672967683545913966173 36239502362881329717737315)
              ·
                refine ⟨54359253544321994576605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36239502362881329717737315 54359253544321994576605973)
                ·
                  refine ⟨2548090009890093495778405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54359253544321994576605973 2548090009890093495778405)
                  ·
                    refine ⟨477766876854392530458451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548090009890093495778405 477766876854392530458451)
                    ·
                      rfl

theorem cell23_2791343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_2791343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791343 prefixEnd_2791343 := by exact prefixLift 2791343
  have htrace : WordTrace (prefixWord ++ tailWord_2791343) baseStart_2791343 baseEnd_2791343 := by
    simpa [prefixWord, tailWord_2791343, baseEnd_2791343] using wordTrace_append hprefix tailTrace_2791343
  have hstable : (prefixWord ++ tailWord_2791343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791343).length < 2 ^ (prefixWord ++ tailWord_2791343).sum := by decide
  have hdescent : baseEnd_2791343 < baseStart_2791343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791360 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_2791360 : Nat := 118140960795 + 2791360 * 2 ^ 59
def prefixEnd_2791360 : Nat := 4983230072969 + 3 ^ 40 * 2791360 * 2
def baseEnd_2791360 : Nat := 477769786578101341620925

theorem tailTrace_2791360 : CollatzResearch.WordTrace tailWord_2791360 prefixEnd_2791360 477769786578101341620925 := by
  unfold tailWord_2791360
  simp only [CollatzResearch.WordTrace]
  refine ⟨50904631583693460589493767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67872842111591280785991689 50904631583693460589493767)
  ·
    refine ⟨76356947375540190884240651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50904631583693460589493767 76356947375540190884240651)
    ·
      refine ⟨114535421063310286326360977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76356947375540190884240651 114535421063310286326360977)
      ·
        refine ⟨85901565797482714744770733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114535421063310286326360977 85901565797482714744770733)
        ·
          refine ⟨32213087174056018029289025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85901565797482714744770733 32213087174056018029289025)
          ·
            refine ⟨24159815380542013521966769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32213087174056018029289025 24159815380542013521966769)
            ·
              refine ⟨18119861535406510141475077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24159815380542013521966769 18119861535406510141475077)
              ·
                refine ⟨3397474037888720651526577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18119861535406510141475077 3397474037888720651526577)
                ·
                  refine ⟨2548105528416540488644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397474037888720651526577 2548105528416540488644933)
                  ·
                    refine ⟨477769786578101341620925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548105528416540488644933 477769786578101341620925)
                    ·
                      rfl

theorem cell23_2791360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_2791360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791360 prefixEnd_2791360 := by exact prefixLift 2791360
  have htrace : WordTrace (prefixWord ++ tailWord_2791360) baseStart_2791360 baseEnd_2791360 := by
    simpa [prefixWord, tailWord_2791360, baseEnd_2791360] using wordTrace_append hprefix tailTrace_2791360
  have hstable : (prefixWord ++ tailWord_2791360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791360).length < 2 ^ (prefixWord ++ tailWord_2791360).sum := by decide
  have hdescent : baseEnd_2791360 < baseStart_2791360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791380 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2791380 : Nat := 118140960795 + 2791380 * 2 ^ 59
def prefixEnd_2791380 : Nat := 4983230072969 + 3 ^ 40 * 2791380 * 2
def baseEnd_2791380 : Nat := 1433319629347393946612683

theorem tailTrace_2791380 : CollatzResearch.WordTrace tailWord_2791380 prefixEnd_2791380 1433319629347393946612683 := by
  unfold tailWord_2791380
  simp only [CollatzResearch.WordTrace]
  refine ⟨50904996313657232297357797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67873328418209643063143729 50904996313657232297357797)
  ·
    refine ⟨9544686808810731055754587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50904996313657232297357797 9544686808810731055754587)
    ·
      refine ⟨14317030213216096583631881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9544686808810731055754587 14317030213216096583631881)
      ·
        refine ⟨10737772659912072437723911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14317030213216096583631881 10737772659912072437723911)
        ·
          refine ⟨16106658989868108656585867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10737772659912072437723911 16106658989868108656585867)
          ·
            refine ⟨24159988484802162984878801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16106658989868108656585867 24159988484802162984878801)
            ·
              refine ⟨18119991363601622238659101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24159988484802162984878801 18119991363601622238659101)
              ·
                refine ⟨6794996761350608339497163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18119991363601622238659101 6794996761350608339497163)
                ·
                  refine ⟨10192495142025912509245745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794996761350608339497163 10192495142025912509245745)
                  ·
                    refine ⟨7644371356519434381934309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10192495142025912509245745 7644371356519434381934309)
                    ·
                      refine ⟨1433319629347393946612683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7644371356519434381934309 1433319629347393946612683)
                      ·
                        rfl

theorem cell23_2791380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2791380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791380 prefixEnd_2791380 := by exact prefixLift 2791380
  have htrace : WordTrace (prefixWord ++ tailWord_2791380) baseStart_2791380 baseEnd_2791380 := by
    simpa [prefixWord, tailWord_2791380, baseEnd_2791380] using wordTrace_append hprefix tailTrace_2791380
  have hstable : (prefixWord ++ tailWord_2791380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791380).length < 2 ^ (prefixWord ++ tailWord_2791380).sum := by decide
  have hdescent : baseEnd_2791380 < baseStart_2791380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791388 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2791388 : Nat := 118140960795 + 2791388 * 2 ^ 59
def prefixEnd_2791388 : Nat := 4983230072969 + 3 ^ 40 * 2791388 * 2
def baseEnd_2791388 : Nat := 1433323737192629915312647

theorem tailTrace_2791388 : CollatzResearch.WordTrace tailWord_2791388 prefixEnd_2791388 1433323737192629915312647 := by
  unfold tailWord_2791388
  simp only [CollatzResearch.WordTrace]
  refine ⟨50905142205642740980503409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67873522940856987974004545 50905142205642740980503409)
  ·
    refine ⟨38178856654232055735377557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50905142205642740980503409 38178856654232055735377557)
    ·
      refine ⟨1789633905667127612595823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38178856654232055735377557 1789633905667127612595823)
      ·
        refine ⟨2684450858500691418893735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789633905667127612595823 2684450858500691418893735)
        ·
          refine ⟨4026676287751037128340603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684450858500691418893735 4026676287751037128340603)
          ·
            refine ⟨6040014431626555692510905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026676287751037128340603 6040014431626555692510905)
            ·
              refine ⟨4530010823719916769383179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040014431626555692510905 4530010823719916769383179)
              ·
                refine ⟨6795016235579875154074769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530010823719916769383179 6795016235579875154074769)
                ·
                  refine ⟨5096262176684906365556077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795016235579875154074769 5096262176684906365556077)
                  ·
                    refine ⟨1911098316256839887083529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5096262176684906365556077 1911098316256839887083529)
                    ·
                      refine ⟨1433323737192629915312647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911098316256839887083529 1433323737192629915312647)
                      ·
                        rfl

theorem cell23_2791388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2791388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791388 prefixEnd_2791388 := by exact prefixLift 2791388
  have htrace : WordTrace (prefixWord ++ tailWord_2791388) baseStart_2791388 baseEnd_2791388 := by
    simpa [prefixWord, tailWord_2791388, baseEnd_2791388] using wordTrace_append hprefix tailTrace_2791388
  have hstable : (prefixWord ++ tailWord_2791388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791388).length < 2 ^ (prefixWord ++ tailWord_2791388).sum := by decide
  have hdescent : baseEnd_2791388 < baseStart_2791388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791417 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2791417 : Nat := 118140960795 + 2791417 * 2 ^ 59
def prefixEnd_2791417 : Nat := 4983230072969 + 3 ^ 40 * 2791417 * 2
def baseEnd_2791417 : Nat := 1433338628131610301850013

theorem tailTrace_2791417 : CollatzResearch.WordTrace tailWord_2791417 prefixEnd_2791417 1433338628131610301850013 := by
  unfold tailWord_2791417
  simp only [CollatzResearch.WordTrace]
  refine ⟨101811342128180419913812505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67874228085453613275875003 101811342128180419913812505)
  ·
    refine ⟨76358506596135314935359379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101811342128180419913812505 76358506596135314935359379)
    ·
      refine ⟨114537759894202972403039069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76358506596135314935359379 114537759894202972403039069)
      ·
        refine ⟨42951659960326114651139651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114537759894202972403039069 42951659960326114651139651)
        ·
          refine ⟨64427489940489171976709477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42951659960326114651139651 64427489940489171976709477)
          ·
            refine ⟨12080154363841719745633027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64427489940489171976709477 12080154363841719745633027)
            ·
              refine ⟨18120231545762579618449541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12080154363841719745633027 18120231545762579618449541)
              ·
                refine ⟨3397543414830483678459289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18120231545762579618449541 3397543414830483678459289)
                ·
                  refine ⟨2548157561122862758844467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397543414830483678459289 2548157561122862758844467)
                  ·
                    refine ⟨3822236341684294138266701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548157561122862758844467 3822236341684294138266701)
                    ·
                      refine ⟨1433338628131610301850013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822236341684294138266701 1433338628131610301850013)
                      ·
                        rfl

theorem cell23_2791417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2791417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791417 prefixEnd_2791417 := by exact prefixLift 2791417
  have htrace : WordTrace (prefixWord ++ tailWord_2791417) baseStart_2791417 baseEnd_2791417 := by
    simpa [prefixWord, tailWord_2791417, baseEnd_2791417] using wordTrace_append hprefix tailTrace_2791417
  have hstable : (prefixWord ++ tailWord_2791417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791417).length < 2 ^ (prefixWord ++ tailWord_2791417).sum := by decide
  have hdescent : baseEnd_2791417 < baseStart_2791417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2]
def baseStart_2791440 : Nat := 118140960795 + 2791440 * 2 ^ 59
def prefixEnd_2791440 : Nat := 4983230072969 + 3 ^ 40 * 2791440 * 2
def baseEnd_2791440 : Nat := 1433350438186663711862407

theorem tailTrace_2791440 : CollatzResearch.WordTrace tailWord_2791440 prefixEnd_2791440 1433350438186663711862407 := by
  unfold tailWord_2791440
  simp only [CollatzResearch.WordTrace]
  refine ⟨50906090503548547420949887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67874787338064729894599849 50906090503548547420949887)
  ·
    refine ⟨76359135755322821131424831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50906090503548547420949887 76359135755322821131424831)
    ·
      refine ⟨114538703632984231697137247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76359135755322821131424831 114538703632984231697137247)
      ·
        refine ⟨171808055449476347545705871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114538703632984231697137247 171808055449476347545705871)
        ·
          refine ⟨257712083174214521318558807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171808055449476347545705871 257712083174214521318558807)
          ·
            refine ⟨386568124761321781977838211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257712083174214521318558807 386568124761321781977838211)
            ·
              refine ⟨579852187141982672966757317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386568124761321781977838211 579852187141982672966757317)
              ·
                refine ⟨108722285089121751181266997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579852187141982672966757317 108722285089121751181266997)
                ·
                  refine ⟨10192714227105164173243781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108722285089121751181266997 10192714227105164173243781)
                  ·
                    refine ⟨1911133917582218282483209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10192714227105164173243781 1911133917582218282483209)
                    ·
                      refine ⟨1433350438186663711862407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911133917582218282483209 1433350438186663711862407)
                      ·
                        rfl

theorem cell23_2791440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2].length) (baseStart_2791440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791440 prefixEnd_2791440 := by exact prefixLift 2791440
  have htrace : WordTrace (prefixWord ++ tailWord_2791440) baseStart_2791440 baseEnd_2791440 := by
    simpa [prefixWord, tailWord_2791440, baseEnd_2791440] using wordTrace_append hprefix tailTrace_2791440
  have hstable : (prefixWord ++ tailWord_2791440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791440).length < 2 ^ (prefixWord ++ tailWord_2791440).sum := by decide
  have hdescent : baseEnd_2791440 < baseStart_2791440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791443 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_2791443 : Nat := 118140960795 + 2791443 * 2 ^ 59
def prefixEnd_2791443 : Nat := 4983230072969 + 3 ^ 40 * 2791443 * 2
def baseEnd_2791443 : Nat := 1433351978628627200124893

theorem tailTrace_2791443 : CollatzResearch.WordTrace tailWord_2791443 prefixEnd_2791443 1433351978628627200124893 := by
  unfold tailWord_2791443
  simp only [CollatzResearch.WordTrace]
  refine ⟨101812290426086226354258983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67874860284057484236172655 101812290426086226354258983)
  ·
    refine ⟨152718435639129339531388475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101812290426086226354258983 152718435639129339531388475)
    ·
      refine ⟨229077653458694009297082713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152718435639129339531388475 229077653458694009297082713)
      ·
        refine ⟨171808240094020506972812035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229077653458694009297082713 171808240094020506972812035)
        ·
          refine ⟨257712360141030760459218053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171808240094020506972812035 257712360141030760459218053)
          ·
            refine ⟨48321067526443267586103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257712360141030760459218053 48321067526443267586103385)
            ·
              refine ⟨36240800644832450689577539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48321067526443267586103385 36240800644832450689577539)
              ·
                refine ⟨54361200967248676034366309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36240800644832450689577539 54361200967248676034366309)
                ·
                  refine ⟨10192725181359126756443683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54361200967248676034366309 10192725181359126756443683)
                  ·
                    refine ⟨15289087772038690134665525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10192725181359126756443683 15289087772038690134665525)
                    ·
                      refine ⟨1433351978628627200124893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15289087772038690134665525 1433351978628627200124893)
                      ·
                        rfl

theorem cell23_2791443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_2791443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791443 prefixEnd_2791443 := by exact prefixLift 2791443
  have htrace : WordTrace (prefixWord ++ tailWord_2791443) baseStart_2791443 baseEnd_2791443 := by
    simpa [prefixWord, tailWord_2791443, baseEnd_2791443] using wordTrace_append hprefix tailTrace_2791443
  have hstable : (prefixWord ++ tailWord_2791443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791443).length < 2 ^ (prefixWord ++ tailWord_2791443).sum := by decide
  have hdescent : baseEnd_2791443 < baseStart_2791443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791461 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_2791461 : Nat := 118140960795 + 2791461 * 2 ^ 59
def prefixEnd_2791461 : Nat := 4983230072969 + 3 ^ 40 * 2791461 * 2
def baseEnd_2791461 : Nat := 1433361221280408129699811

theorem tailTrace_2791461 : CollatzResearch.WordTrace tailWord_2791461 prefixEnd_2791461 1433361221280408129699811 := by
  unfold tailWord_2791461
  simp only [CollatzResearch.WordTrace]
  refine ⟨101812946940021015428414237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67875297960014010285609491 101812946940021015428414237)
  ·
    refine ⟨38179855102507880785655339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101812946940021015428414237 38179855102507880785655339)
    ·
      refine ⟨57269782653761821178483009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38179855102507880785655339 57269782653761821178483009)
      ·
        refine ⟨42952336990321365883862257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57269782653761821178483009 42952336990321365883862257)
        ·
          refine ⟨32214252742741024412896693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42952336990321365883862257 32214252742741024412896693)
          ·
            refine ⟨3020086194631971038709065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32214252742741024412896693 3020086194631971038709065)
            ·
              refine ⟨2265064645973978279031799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020086194631971038709065 2265064645973978279031799)
              ·
                refine ⟨3397596968960967418547699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265064645973978279031799 3397596968960967418547699)
                ·
                  refine ⟨5096395453441451127821549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397596968960967418547699 5096395453441451127821549)
                  ·
                    refine ⟨1911148295040544172933081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5096395453441451127821549 1911148295040544172933081)
                    ·
                      refine ⟨1433361221280408129699811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911148295040544172933081 1433361221280408129699811)
                      ·
                        rfl

theorem cell23_2791461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_2791461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791461 prefixEnd_2791461 := by exact prefixLift 2791461
  have htrace : WordTrace (prefixWord ++ tailWord_2791461) baseStart_2791461 baseEnd_2791461 := by
    simpa [prefixWord, tailWord_2791461, baseEnd_2791461] using wordTrace_append hprefix tailTrace_2791461
  have hstable : (prefixWord ++ tailWord_2791461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791461).length < 2 ^ (prefixWord ++ tailWord_2791461).sum := by decide
  have hdescent : baseEnd_2791461 < baseStart_2791461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791474 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_2791474 : Nat := 118140960795 + 2791474 * 2 ^ 59
def prefixEnd_2791474 : Nat := 4983230072969 + 3 ^ 40 * 2791474 * 2
def baseEnd_2791474 : Nat := 1433367896528916578837251

theorem tailTrace_2791474 : CollatzResearch.WordTrace tailWord_2791474 prefixEnd_2791474 1433367896528916578837251 := by
  unfold tailWord_2791474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453355272243479662159369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67875614059315945765758317 25453355272243479662159369)
  ·
    refine ⟨19090016454182609746619527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25453355272243479662159369 19090016454182609746619527)
    ·
      refine ⟨28635024681273914619929291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19090016454182609746619527 28635024681273914619929291)
      ·
        refine ⟨42952537021910871929893937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28635024681273914619929291 42952537021910871929893937)
        ·
          refine ⟨32214402766433153947420453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42952537021910871929893937 32214402766433153947420453)
          ·
            refine ⟨6040200518706216365141335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32214402766433153947420453 6040200518706216365141335)
            ·
              refine ⟨9060300778059324547712003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040200518706216365141335 9060300778059324547712003)
              ·
                refine ⟨13590451167088986821568005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060300778059324547712003 13590451167088986821568005)
                ·
                  refine ⟨2548209593829185029044001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13590451167088986821568005 2548209593829185029044001)
                  ·
                    refine ⟨1911157195371888771783001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2548209593829185029044001 1911157195371888771783001)
                    ·
                      refine ⟨1433367896528916578837251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911157195371888771783001 1433367896528916578837251)
                      ·
                        rfl

theorem cell23_2791474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_2791474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791474 prefixEnd_2791474 := by exact prefixLift 2791474
  have htrace : WordTrace (prefixWord ++ tailWord_2791474) baseStart_2791474 baseEnd_2791474 := by
    simpa [prefixWord, tailWord_2791474, baseEnd_2791474] using wordTrace_append hprefix tailTrace_2791474
  have hstable : (prefixWord ++ tailWord_2791474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791474).length < 2 ^ (prefixWord ++ tailWord_2791474).sum := by decide
  have hdescent : baseEnd_2791474 < baseStart_2791474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791503 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_2791503 : Nat := 118140960795 + 2791503 * 2 ^ 59
def prefixEnd_2791503 : Nat := 4983230072969 + 3 ^ 40 * 2791503 * 2
def baseEnd_2791503 : Nat := 1433382787467896965374617

theorem tailTrace_2791503 : CollatzResearch.WordTrace tailWord_2791503 prefixEnd_2791503 1433382787467896965374617 := by
  unfold tailWord_2791503
  simp only [CollatzResearch.WordTrace]
  refine ⟨101814478805868856601443163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67876319203912571067628775 101814478805868856601443163)
  ·
    refine ⟨152721718208803284902164745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101814478805868856601443163 152721718208803284902164745)
    ·
      refine ⟨114541288656602463676623559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152721718208803284902164745 114541288656602463676623559)
      ·
        refine ⟨171811932984903695514935339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114541288656602463676623559 171811932984903695514935339)
        ·
          refine ⟨257717899477355543272403009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171811932984903695514935339 257717899477355543272403009)
          ·
            refine ⟨193288424608016657454302257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257717899477355543272403009 193288424608016657454302257)
            ·
              refine ⟨144966318456012493090726693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193288424608016657454302257 144966318456012493090726693)
              ·
                refine ⟨27181184710502342454511255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144966318456012493090726693 27181184710502342454511255)
                ·
                  refine ⟨40771777065753513681766883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27181184710502342454511255 40771777065753513681766883)
                  ·
                    refine ⟨61157665598630270522650325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40771777065753513681766883 61157665598630270522650325)
                    ·
                      refine ⟨1433382787467896965374617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61157665598630270522650325 1433382787467896965374617)
                      ·
                        rfl

theorem cell23_2791503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_2791503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791503 prefixEnd_2791503 := by exact prefixLift 2791503
  have htrace : WordTrace (prefixWord ++ tailWord_2791503) baseStart_2791503 baseEnd_2791503 := by
    simpa [prefixWord, tailWord_2791503, baseEnd_2791503] using wordTrace_append hprefix tailTrace_2791503
  have hstable : (prefixWord ++ tailWord_2791503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791503).length < 2 ^ (prefixWord ++ tailWord_2791503).sum := by decide
  have hdescent : baseEnd_2791503 < baseStart_2791503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791598 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2791598 : Nat := 118140960795 + 2791598 * 2 ^ 59
def prefixEnd_2791598 : Nat := 4983230072969 + 3 ^ 40 * 2791598 * 2
def baseEnd_2791598 : Nat := 1433431568130074093686681

theorem tailTrace_2791598 : CollatzResearch.WordTrace tailWord_2791598 prefixEnd_2791598 1433431568130074093686681 := by
  unfold tailWord_2791598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727242967565585978268931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67878629160349791884100965 12727242967565585978268931)
  ·
    refine ⟨19090864451348378967403397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12727242967565585978268931 19090864451348378967403397)
    ·
      refine ⟨3579537084627821056388137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19090864451348378967403397 3579537084627821056388137)
      ·
        refine ⟨2684652813470865792291103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3579537084627821056388137 2684652813470865792291103)
        ·
          refine ⟨4026979220206298688436655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684652813470865792291103 4026979220206298688436655)
          ·
            refine ⟨6040468830309448032654983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026979220206298688436655 6040468830309448032654983)
            ·
              refine ⟨9060703245464172048982475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040468830309448032654983 9060703245464172048982475)
              ·
                refine ⟨13591054868196258073473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060703245464172048982475 13591054868196258073473713)
                ·
                  refine ⟨10193291151147193555105285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13591054868196258073473713 10193291151147193555105285)
                  ·
                    refine ⟨1911242090840098791582241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10193291151147193555105285 1911242090840098791582241)
                    ·
                      refine ⟨1433431568130074093686681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911242090840098791582241 1433431568130074093686681)
                      ·
                        rfl

theorem cell23_2791598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2791598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791598 prefixEnd_2791598 := by exact prefixLift 2791598
  have htrace : WordTrace (prefixWord ++ tailWord_2791598) baseStart_2791598 baseEnd_2791598 := by
    simpa [prefixWord, tailWord_2791598, baseEnd_2791598] using wordTrace_append hprefix tailTrace_2791598
  have hstable : (prefixWord ++ tailWord_2791598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791598).length < 2 ^ (prefixWord ++ tailWord_2791598).sum := by decide
  have hdescent : baseEnd_2791598 < baseStart_2791598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791618 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2791618 : Nat := 118140960795 + 2791618 * 2 ^ 59
def prefixEnd_2791618 : Nat := 4983230072969 + 3 ^ 40 * 2791618 * 2
def baseEnd_2791618 : Nat := 1433441837743164015436589

theorem tailTrace_2791618 : CollatzResearch.WordTrace tailWord_2791618 prefixEnd_2791618 1433441837743164015436589 := by
  unfold tailWord_2791618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25454668300113057810469877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67879115466968154161253005 25454668300113057810469877)
  ·
    refine ⟨2386375153135599169731551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25454668300113057810469877 2386375153135599169731551)
    ·
      refine ⟨3579562729703398754597327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386375153135599169731551 3579562729703398754597327)
      ·
        refine ⟨5369344094555098131895991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579562729703398754597327 5369344094555098131895991)
        ·
          refine ⟨8054016141832647197843987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369344094555098131895991 8054016141832647197843987)
          ·
            refine ⟨12081024212748970796765981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054016141832647197843987 12081024212748970796765981)
            ·
              refine ⟨4530384079780864048787243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12081024212748970796765981 4530384079780864048787243)
              ·
                refine ⟨6795576119671296073180865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530384079780864048787243 6795576119671296073180865)
                ·
                  refine ⟨5096682089753472054885649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795576119671296073180865 5096682089753472054885649)
                  ·
                    refine ⟨3822511567315104041164237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096682089753472054885649 3822511567315104041164237)
                    ·
                      refine ⟨1433441837743164015436589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822511567315104041164237 1433441837743164015436589)
                      ·
                        rfl

theorem cell23_2791618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2791618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791618 prefixEnd_2791618 := by exact prefixLift 2791618
  have htrace : WordTrace (prefixWord ++ tailWord_2791618) baseStart_2791618 baseEnd_2791618 := by
    simpa [prefixWord, tailWord_2791618, baseEnd_2791618] using wordTrace_append hprefix tailTrace_2791618
  have hstable : (prefixWord ++ tailWord_2791618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791618).length < 2 ^ (prefixWord ++ tailWord_2791618).sum := by decide
  have hdescent : baseEnd_2791618 < baseStart_2791618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791631 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 1, 1, 3]
def baseStart_2791631 : Nat := 118140960795 + 2791631 * 2 ^ 59
def prefixEnd_2791631 : Nat := 4983230072969 + 3 ^ 40 * 2791631 * 2
def baseEnd_2791631 : Nat := 1433448512991672464574029

theorem tailTrace_2791631 : CollatzResearch.WordTrace tailWord_2791631 prefixEnd_2791631 1433448512991672464574029 := by
  unfold tailWord_2791631
  simp only [CollatzResearch.WordTrace]
  refine ⟨101819147349405134462102747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67879431566270089641401831 101819147349405134462102747)
  ·
    refine ⟨152728721024107701693154121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101819147349405134462102747 152728721024107701693154121)
    ·
      refine ⟨114546540768080776269865591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152728721024107701693154121 114546540768080776269865591)
      ·
        refine ⟨171819811152121164404798387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114546540768080776269865591 171819811152121164404798387)
        ·
          refine ⟨257729716728181746607197581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171819811152121164404798387 257729716728181746607197581)
          ·
            refine ⟨96648643773068154977699093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257729716728181746607197581 96648643773068154977699093)
            ·
              refine ⟨4530405176862569764579645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96648643773068154977699093 4530405176862569764579645)
              ·
                refine ⟨1698901941323463661717367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4530405176862569764579645 1698901941323463661717367)
                ·
                  refine ⟨2548352911985195492576051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698901941323463661717367 2548352911985195492576051)
                  ·
                    refine ⟨3822529367977793238864077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548352911985195492576051 3822529367977793238864077)
                    ·
                      refine ⟨1433448512991672464574029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822529367977793238864077 1433448512991672464574029)
                      ·
                        rfl

theorem cell23_2791631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 1, 3].length) (baseStart_2791631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791631 prefixEnd_2791631 := by exact prefixLift 2791631
  have htrace : WordTrace (prefixWord ++ tailWord_2791631) baseStart_2791631 baseEnd_2791631 := by
    simpa [prefixWord, tailWord_2791631, baseEnd_2791631] using wordTrace_append hprefix tailTrace_2791631
  have hstable : (prefixWord ++ tailWord_2791631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791631).length < 2 ^ (prefixWord ++ tailWord_2791631).sum := by decide
  have hdescent : baseEnd_2791631 < baseStart_2791631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791634 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2791634 : Nat := 118140960795 + 2791634 * 2 ^ 59
def prefixEnd_2791634 : Nat := 4983230072969 + 3 ^ 40 * 2791634 * 2
def baseEnd_2791634 : Nat := 477816684477878650945505

theorem tailTrace_2791634 : CollatzResearch.WordTrace tailWord_2791634 prefixEnd_2791634 477816684477878650945505 := by
  unfold tailWord_2791634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25454814192098566493615489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67879504512262843982974637 25454814192098566493615489)
  ·
    refine ⟨19091110644073924870211617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25454814192098566493615489 19091110644073924870211617)
    ·
      refine ⟨14318332983055443652658713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19091110644073924870211617 14318332983055443652658713)
      ·
        refine ⟨10738749737291582739494035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14318332983055443652658713 10738749737291582739494035)
        ·
          refine ⟨16108124605937374109241053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10738749737291582739494035 16108124605937374109241053)
          ·
            refine ⟨6040546727226515290965395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16108124605937374109241053 6040546727226515290965395)
            ·
              refine ⟨9060820090839772936448093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040546727226515290965395 9060820090839772936448093)
              ·
                refine ⟨3397807534064914851168035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9060820090839772936448093 3397807534064914851168035)
                ·
                  refine ⟨5096711301097372276752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397807534064914851168035 5096711301097372276752053)
                  ·
                    refine ⟨477816684477878650945505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5096711301097372276752053 477816684477878650945505)
                    ·
                      rfl

theorem cell23_2791634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2791634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791634 prefixEnd_2791634 := by exact prefixLift 2791634
  have htrace : WordTrace (prefixWord ++ tailWord_2791634) baseStart_2791634 baseEnd_2791634 := by
    simpa [prefixWord, tailWord_2791634, baseEnd_2791634] using wordTrace_append hprefix tailTrace_2791634
  have hstable : (prefixWord ++ tailWord_2791634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791634).length < 2 ^ (prefixWord ++ tailWord_2791634).sum := by decide
  have hdescent : baseEnd_2791634 < baseStart_2791634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791660 : List Nat := [2, 2, 1, 1, 2, 3, 2, 10]
def baseStart_2791660 : Nat := 118140960795 + 2791660 * 2 ^ 59
def prefixEnd_2791660 : Nat := 4983230072969 + 3 ^ 40 * 2791660 * 2
def baseEnd_2791660 : Nat := 53091237182616772263385

theorem tailTrace_2791660 : CollatzResearch.WordTrace tailWord_2791660 prefixEnd_2791660 53091237182616772263385 := by
  unfold tailWord_2791660
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910102533150036207454217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67880136710866714943272289 50910102533150036207454217)
  ·
    refine ⟨38182576899862527155590663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50910102533150036207454217 38182576899862527155590663)
    ·
      refine ⟨57273865349793790733385995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38182576899862527155590663 57273865349793790733385995)
      ·
        refine ⟨85910798024690686100078993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57273865349793790733385995 85910798024690686100078993)
        ·
          refine ⟨64433098518518014575059245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85910798024690686100078993 64433098518518014575059245)
          ·
            refine ⟨24162411944444255465647217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64433098518518014575059245 24162411944444255465647217)
            ·
              refine ⟨18121808958333191599235413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24162411944444255465647217 18121808958333191599235413)
              ·
                refine ⟨53091237182616772263385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18121808958333191599235413 53091237182616772263385)
                ·
                  rfl

theorem cell23_2791660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 10].length) (baseStart_2791660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791660 prefixEnd_2791660 := by exact prefixLift 2791660
  have htrace : WordTrace (prefixWord ++ tailWord_2791660) baseStart_2791660 baseEnd_2791660 := by
    simpa [prefixWord, tailWord_2791660, baseEnd_2791660] using wordTrace_append hprefix tailTrace_2791660
  have hstable : (prefixWord ++ tailWord_2791660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791660).length < 2 ^ (prefixWord ++ tailWord_2791660).sum := by decide
  have hdescent : baseEnd_2791660 < baseStart_2791660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791674 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_2791674 : Nat := 118140960795 + 2791674 * 2 ^ 59
def prefixEnd_2791674 : Nat := 4983230072969 + 3 ^ 40 * 2791674 * 2
def baseEnd_2791674 : Nat := 1433470592659815796336331

theorem tailTrace_2791674 : CollatzResearch.WordTrace tailWord_2791674 prefixEnd_2791674 1433470592659815796336331 := by
  unfold tailWord_2791674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25455178922062338201479519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67880477125499568537278717 25455178922062338201479519)
  ·
    refine ⟨38182768383093507302219279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25455178922062338201479519 38182768383093507302219279)
    ·
      refine ⟨57274152574640260953328919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38182768383093507302219279 57274152574640260953328919)
      ·
        refine ⟨85911228861960391429993379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57274152574640260953328919 85911228861960391429993379)
        ·
          refine ⟨128866843292940587144990069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85911228861960391429993379 128866843292940587144990069)
          ·
            refine ⟨12081266558713180044842819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128866843292940587144990069 12081266558713180044842819)
            ·
              refine ⟨18121899838069770067264229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081266558713180044842819 18121899838069770067264229)
              ·
                refine ⟨3397856219638081887612043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18121899838069770067264229 3397856219638081887612043)
                ·
                  refine ⟨5096784329457122831418065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397856219638081887612043 5096784329457122831418065)
                  ·
                    refine ⟨3822588247092842123563549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096784329457122831418065 3822588247092842123563549)
                    ·
                      refine ⟨1433470592659815796336331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822588247092842123563549 1433470592659815796336331)
                      ·
                        rfl

theorem cell23_2791674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_2791674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791674 prefixEnd_2791674 := by exact prefixLift 2791674
  have htrace : WordTrace (prefixWord ++ tailWord_2791674) baseStart_2791674 baseEnd_2791674 := by
    simpa [prefixWord, tailWord_2791674, baseEnd_2791674] using wordTrace_append hprefix tailTrace_2791674
  have hstable : (prefixWord ++ tailWord_2791674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791674).length < 2 ^ (prefixWord ++ tailWord_2791674).sum := by decide
  have hdescent : baseEnd_2791674 < baseStart_2791674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791704 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2791704 : Nat := 118140960795 + 2791704 * 2 ^ 59
def prefixEnd_2791704 : Nat := 4983230072969 + 3 ^ 40 * 2791704 * 2
def baseEnd_2791704 : Nat := 1433485997079450678961193

theorem tailTrace_2791704 : CollatzResearch.WordTrace tailWord_2791704 prefixEnd_2791704 1433485997079450678961193 := by
  unfold tailWord_2791704
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910904939070333964755083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67881206585427111953006777 50910904939070333964755083)
  ·
    refine ⟨76366357408605500947132625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50910904939070333964755083 76366357408605500947132625)
    ·
      refine ⟨57274768056454125710349469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76366357408605500947132625 57274768056454125710349469)
      ·
        refine ⟨21478038021170297141381051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57274768056454125710349469 21478038021170297141381051)
        ·
          refine ⟨32217057031755445712071577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21478038021170297141381051 32217057031755445712071577)
          ·
            refine ⟨24162792773816584284053683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32217057031755445712071577 24162792773816584284053683)
            ·
              refine ⟨36244189160724876426080525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24162792773816584284053683 36244189160724876426080525)
              ·
                refine ⟨13591570935271828659780197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36244189160724876426080525 13591570935271828659780197)
                ·
                  refine ⟨2548419550363467873708787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13591570935271828659780197 2548419550363467873708787)
                  ·
                    refine ⟨3822629325545201810563181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2548419550363467873708787 3822629325545201810563181)
                    ·
                      refine ⟨1433485997079450678961193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822629325545201810563181 1433485997079450678961193)
                      ·
                        rfl

theorem cell23_2791704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2791704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791704 prefixEnd_2791704 := by exact prefixLift 2791704
  have htrace : WordTrace (prefixWord ++ tailWord_2791704) baseStart_2791704 baseEnd_2791704 := by
    simpa [prefixWord, tailWord_2791704, baseEnd_2791704] using wordTrace_append hprefix tailTrace_2791704
  have hstable : (prefixWord ++ tailWord_2791704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791704).length < 2 ^ (prefixWord ++ tailWord_2791704).sum := by decide
  have hdescent : baseEnd_2791704 < baseStart_2791704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791725 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2791725 : Nat := 118140960795 + 2791725 * 2 ^ 59
def prefixEnd_2791725 : Nat := 4983230072969 + 3 ^ 40 * 2791725 * 2
def baseEnd_2791725 : Nat := 1433496780173195096798597

theorem tailTrace_2791725 : CollatzResearch.WordTrace tailWord_2791725 prefixEnd_2791725 1433496780173195096798597 := by
  unfold tailWord_2791725
  simp only [CollatzResearch.WordTrace]
  refine ⟨101822575811064588516024629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67881717207376392344016419 101822575811064588516024629)
  ·
    refine ⟨9545866482287305173377309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101822575811064588516024629 9545866482287305173377309)
    ·
      refine ⟨3579699930857739440016491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9545866482287305173377309 3579699930857739440016491)
      ·
        refine ⟨5369549896286609160024737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579699930857739440016491 5369549896286609160024737)
        ·
          refine ⟨4027162422214956870018553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5369549896286609160024737 4027162422214956870018553)
          ·
            refine ⟨3020371816661217652513915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027162422214956870018553 3020371816661217652513915)
            ·
              refine ⟨4530557724991826478770873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020371816661217652513915 4530557724991826478770873)
              ·
                refine ⟨3397918293743869859078155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530557724991826478770873 3397918293743869859078155)
                ·
                  refine ⟨5096877440615804788617233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397918293743869859078155 5096877440615804788617233)
                  ·
                    refine ⟨3822658080461853591462925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5096877440615804788617233 3822658080461853591462925)
                    ·
                      refine ⟨1433496780173195096798597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822658080461853591462925 1433496780173195096798597)
                      ·
                        rfl

theorem cell23_2791725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2791725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791725 prefixEnd_2791725 := by exact prefixLift 2791725
  have htrace : WordTrace (prefixWord ++ tailWord_2791725) baseStart_2791725 baseEnd_2791725 := by
    simpa [prefixWord, tailWord_2791725, baseEnd_2791725] using wordTrace_append hprefix tailTrace_2791725
  have hstable : (prefixWord ++ tailWord_2791725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791725).length < 2 ^ (prefixWord ++ tailWord_2791725).sum := by decide
  have hdescent : baseEnd_2791725 < baseStart_2791725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791747 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_2791747 : Nat := 118140960795 + 2791747 * 2 ^ 59
def prefixEnd_2791747 : Nat := 4983230072969 + 3 ^ 40 * 2791747 * 2
def baseEnd_2791747 : Nat := 1433508076747594010723495

theorem tailTrace_2791747 : CollatzResearch.WordTrace tailWord_2791747 prefixEnd_2791747 1433508076747594010723495 := by
  unfold tailWord_2791747
  simp only [CollatzResearch.WordTrace]
  refine ⟨101823378216984886273325495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67882252144656590848883663 101823378216984886273325495)
  ·
    refine ⟨152735067325477329409988243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101823378216984886273325495 152735067325477329409988243)
    ·
      refine ⟨229102600988215994114982365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152735067325477329409988243 229102600988215994114982365)
      ·
        refine ⟨85913475370580997793118387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229102600988215994114982365 85913475370580997793118387)
        ·
          refine ⟨128870213055871496689677581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85913475370580997793118387 128870213055871496689677581)
          ·
            refine ⟨48326329895951811258629093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128870213055871496689677581 48326329895951811258629093)
            ·
              refine ⟨9061186855490964610992955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48326329895951811258629093 9061186855490964610992955)
              ·
                refine ⟨13591780283236446916489433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9061186855490964610992955 13591780283236446916489433)
                ·
                  refine ⟨10193835212427335187367075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13591780283236446916489433 10193835212427335187367075)
                  ·
                    refine ⟨15290752818641002781050613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10193835212427335187367075 15290752818641002781050613)
                    ·
                      refine ⟨1433508076747594010723495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15290752818641002781050613 1433508076747594010723495)
                      ·
                        rfl

theorem cell23_2791747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_2791747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791747 prefixEnd_2791747 := by exact prefixLift 2791747
  have htrace : WordTrace (prefixWord ++ tailWord_2791747) baseStart_2791747 baseEnd_2791747 := by
    simpa [prefixWord, tailWord_2791747, baseEnd_2791747] using wordTrace_append hprefix tailTrace_2791747
  have hstable : (prefixWord ++ tailWord_2791747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791747).length < 2 ^ (prefixWord ++ tailWord_2791747).sum := by decide
  have hdescent : baseEnd_2791747 < baseStart_2791747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791764 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2791764 : Nat := 118140960795 + 2791764 * 2 ^ 59
def prefixEnd_2791764 : Nat := 4983230072969 + 3 ^ 40 * 2791764 * 2
def baseEnd_2791764 : Nat := 1433516805918720444210917

theorem tailTrace_2791764 : CollatzResearch.WordTrace tailWord_2791764 prefixEnd_2791764 1433516805918720444210917 := by
  unfold tailWord_2791764
  simp only [CollatzResearch.WordTrace]
  refine ⟨50911999128961649088347173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67882665505282198784462897 50911999128961649088347173)
  ·
    refine ⟨9545999836680309204065095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50911999128961649088347173 9545999836680309204065095)
    ·
      refine ⟨14318999755020463806097643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545999836680309204065095 14318999755020463806097643)
      ·
        refine ⟨21478499632530695709146465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318999755020463806097643 21478499632530695709146465)
        ·
          refine ⟨16108874724398021781859849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21478499632530695709146465 16108874724398021781859849)
          ·
            refine ⟨12081656043298516336394887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16108874724398021781859849 12081656043298516336394887)
            ·
              refine ⟨18122484064947774504592331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081656043298516336394887 18122484064947774504592331)
              ·
                refine ⟨27183726097421661756888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18122484064947774504592331 27183726097421661756888497)
                ·
                  refine ⟨20387794573066246317666373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27183726097421661756888497 20387794573066246317666373)
                  ·
                    refine ⟨3822711482449921184562445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20387794573066246317666373 3822711482449921184562445)
                    ·
                      refine ⟨1433516805918720444210917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3822711482449921184562445 1433516805918720444210917)
                      ·
                        rfl

theorem cell23_2791764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2791764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791764 prefixEnd_2791764 := by exact prefixLift 2791764
  have htrace : WordTrace (prefixWord ++ tailWord_2791764) baseStart_2791764 baseEnd_2791764 := by
    simpa [prefixWord, tailWord_2791764, baseEnd_2791764] using wordTrace_append hprefix tailTrace_2791764
  have hstable : (prefixWord ++ tailWord_2791764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791764).length < 2 ^ (prefixWord ++ tailWord_2791764).sum := by decide
  have hdescent : baseEnd_2791764 < baseStart_2791764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791767 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 7]
def baseStart_2791767 : Nat := 118140960795 + 2791767 * 2 ^ 59
def prefixEnd_2791767 : Nat := 4983230072969 + 3 ^ 40 * 2791767 * 2
def baseEnd_2791767 : Nat := 159279816262298214719267

theorem tailTrace_2791767 : CollatzResearch.WordTrace tailWord_2791767 prefixEnd_2791767 159279816262298214719267 := by
  unfold tailWord_2791767
  simp only [CollatzResearch.WordTrace]
  refine ⟨101824107676912429689053555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67882738451274953126035703 101824107676912429689053555)
  ·
    refine ⟨152736161515368644533580333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101824107676912429689053555 152736161515368644533580333)
    ·
      refine ⟨57276060568263241700092625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152736161515368644533580333 57276060568263241700092625)
      ·
        refine ⟨42957045426197431275069469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57276060568263241700092625 42957045426197431275069469)
        ·
          refine ⟨16108892034824036728151051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42957045426197431275069469 16108892034824036728151051)
          ·
            refine ⟨24163338052236055092226577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16108892034824036728151051 24163338052236055092226577)
            ·
              refine ⟨18122503539177041319169933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24163338052236055092226577 18122503539177041319169933)
              ·
                refine ⟨6795938827191390494688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18122503539177041319169933 6795938827191390494688725)
                ·
                  refine ⟨159279816262298214719267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6795938827191390494688725 159279816262298214719267)
                  ·
                    rfl

theorem cell23_2791767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 7].length) (baseStart_2791767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791767 prefixEnd_2791767 := by exact prefixLift 2791767
  have htrace : WordTrace (prefixWord ++ tailWord_2791767) baseStart_2791767 baseEnd_2791767 := by
    simpa [prefixWord, tailWord_2791767, baseEnd_2791767] using wordTrace_append hprefix tailTrace_2791767
  have hstable : (prefixWord ++ tailWord_2791767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791767).length < 2 ^ (prefixWord ++ tailWord_2791767).sum := by decide
  have hdescent : baseEnd_2791767 < baseStart_2791767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791778 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2791778 : Nat := 118140960795 + 2791778 * 2 ^ 59
def prefixEnd_2791778 : Nat := 4983230072969 + 3 ^ 40 * 2791778 * 2
def baseEnd_2791778 : Nat := 1433523994647883389435853

theorem tailTrace_2791778 : CollatzResearch.WordTrace tailWord_2791778 prefixEnd_2791778 1433523994647883389435853 := by
  unfold tailWord_2791778
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456127219968144641925997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67883005919915052378469325 25456127219968144641925997)
  ·
    refine ⟨9546047707488054240722249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25456127219968144641925997 9546047707488054240722249)
    ·
      refine ⟨7159535780616040680541687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9546047707488054240722249 7159535780616040680541687)
      ·
        refine ⟨10739303670924061020812531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159535780616040680541687 10739303670924061020812531)
        ·
          refine ⟨16108955506386091531218797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10739303670924061020812531 16108955506386091531218797)
          ·
            refine ⟨6040858314894784324207049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16108955506386091531218797 6040858314894784324207049)
            ·
              refine ⟨4530643736171088243155287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040858314894784324207049 4530643736171088243155287)
              ·
                refine ⟨6795965604256632364732931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530643736171088243155287 6795965604256632364732931)
                ·
                  refine ⟨10193948406384948547099397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6795965604256632364732931 10193948406384948547099397)
                  ·
                    refine ⟨1911365326197177852581137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10193948406384948547099397 1911365326197177852581137)
                    ·
                      refine ⟨1433523994647883389435853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1911365326197177852581137 1433523994647883389435853)
                      ·
                        rfl

theorem cell23_2791778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2791778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791778 prefixEnd_2791778 := by exact prefixLift 2791778
  have htrace : WordTrace (prefixWord ++ tailWord_2791778) baseStart_2791778 baseEnd_2791778 := by
    simpa [prefixWord, tailWord_2791778, baseEnd_2791778] using wordTrace_append hprefix tailTrace_2791778
  have hstable : (prefixWord ++ tailWord_2791778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791778).length < 2 ^ (prefixWord ++ tailWord_2791778).sum := by decide
  have hdescent : baseEnd_2791778 < baseStart_2791778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2791784 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 7]
def baseStart_2791784 : Nat := 118140960795 + 2791784 * 2 ^ 59
def prefixEnd_2791784 : Nat := 4983230072969 + 3 ^ 40 * 2791784 * 2
def baseEnd_2791784 : Nat := 159280786170201151773425

theorem tailTrace_2791784 : CollatzResearch.WordTrace tailWord_2791784 prefixEnd_2791784 159280786170201151773425 := by
  unfold tailWord_2791784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912363858925420796211203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67883151811900561061614937 50912363858925420796211203)
  ·
    refine ⟨76368545788388131194316805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50912363858925420796211203 76368545788388131194316805)
    ·
      refine ⟨14319102335322774598934401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76368545788388131194316805 14319102335322774598934401)
      ·
        refine ⟨10739326751492080949200801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14319102335322774598934401 10739326751492080949200801)
        ·
          refine ⟨8054495063619060711900601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10739326751492080949200801 8054495063619060711900601)
          ·
            refine ⟨6040871297714295533925451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8054495063619060711900601 6040871297714295533925451)
            ·
              refine ⟨9061306946571443300888177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040871297714295533925451 9061306946571443300888177)
              ·
                refine ⟨6795980209928582475666133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9061306946571443300888177 6795980209928582475666133)
                ·
                  refine ⟨159280786170201151773425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6795980209928582475666133 159280786170201151773425)
                  ·
                    rfl

theorem cell23_2791784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_2791784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2791784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2791784 prefixEnd_2791784 := by exact prefixLift 2791784
  have htrace : WordTrace (prefixWord ++ tailWord_2791784) baseStart_2791784 baseEnd_2791784 := by
    simpa [prefixWord, tailWord_2791784, baseEnd_2791784] using wordTrace_append hprefix tailTrace_2791784
  have hstable : (prefixWord ++ tailWord_2791784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2791784).length < 2 ^ (prefixWord ++ tailWord_2791784).sum := by decide
  have hdescent : baseEnd_2791784 < baseStart_2791784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2791784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
