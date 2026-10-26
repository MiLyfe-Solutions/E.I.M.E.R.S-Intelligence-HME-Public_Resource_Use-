import V185TrunkScan22Chunk005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_53739 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_53739 : Nat := 118140960795 + 53739 * 2 ^ 59
def prefixEnd_53739 : Nat := 4983230072969 + 3 ^ 40 * 53739 * 2
def baseEnd_53739 : Nat := 18395957928046986410243

theorem tailTrace_53739 : CollatzResearch.WordTrace tailWord_53739 prefixEnd_53739 18395957928046986410243 := by
  unfold tailWord_53739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960022352320255735620271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1306681568213503823746847 1960022352320255735620271)
  ·
    refine ⟨2940033528480383603430407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960022352320255735620271 2940033528480383603430407)
    ·
      refine ⟨4410050292720575405145611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940033528480383603430407 4410050292720575405145611)
      ·
        refine ⟨6615075439080863107718417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410050292720575405145611 6615075439080863107718417)
        ·
          refine ⟨4961306579310647330788813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615075439080863107718417 4961306579310647330788813)
          ·
            refine ⟨1860489967241492749045805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961306579310647330788813 1860489967241492749045805)
            ·
              refine ⟨697683737715559780892177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860489967241492749045805 697683737715559780892177)
              ·
                refine ⟨523262803286669835669133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697683737715559780892177 523262803286669835669133)
                ·
                  refine ⟨196223551232501188375925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523262803286669835669133 196223551232501188375925)
                  ·
                    refine ⟨18395957928046986410243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196223551232501188375925 18395957928046986410243)
                    ·
                      rfl

theorem cell22_53739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_53739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53739 prefixEnd_53739 := by exact prefixLift 53739
  have htrace : WordTrace (prefixWord ++ tailWord_53739) baseStart_53739 baseEnd_53739 := by
    simpa [prefixWord, tailWord_53739, baseEnd_53739] using wordTrace_append hprefix tailTrace_53739
  have hstable : (prefixWord ++ tailWord_53739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53739).length < 2 ^ (prefixWord ++ tailWord_53739).sum := by decide
  have hdescent : baseEnd_53739 < baseStart_53739 := by decide
  rcases family_descends (prefixWord ++ tailWord_53739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53756 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_53756 : Nat := 118140960795 + 53756 * 2 ^ 59
def prefixEnd_53756 : Nat := 4983230072969 + 3 ^ 40 * 53756 * 2
def baseEnd_53756 : Nat := 18401777375464608735191

theorem tailTrace_53756 : CollatzResearch.WordTrace tailWord_53756 prefixEnd_53756 18401777375464608735191 := by
  unfold tailWord_53756
  simp only [CollatzResearch.WordTrace]
  refine ⟨980321196629333819494561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1307094928839111759326081 980321196629333819494561)
  ·
    refine ⟨735240897472000364620921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 980321196629333819494561 735240897472000364620921)
    ·
      refine ⟨551430673104000273465691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 735240897472000364620921 551430673104000273465691)
      ·
        refine ⟨827146009656000410198537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551430673104000273465691 827146009656000410198537)
        ·
          refine ⟨620359507242000307648903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827146009656000410198537 620359507242000307648903)
          ·
            refine ⟨930539260863000461473355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620359507242000307648903 930539260863000461473355)
            ·
              refine ⟨1395808891294500692210033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930539260863000461473355 1395808891294500692210033)
              ·
                refine ⟨1046856668470875519157525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395808891294500692210033 1046856668470875519157525)
                ·
                  refine ⟨49071406334572289960509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1046856668470875519157525 49071406334572289960509)
                  ·
                    refine ⟨18401777375464608735191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49071406334572289960509 18401777375464608735191)
                    ·
                      rfl

theorem cell22_53756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_53756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53756 prefixEnd_53756 := by exact prefixLift 53756
  have htrace : WordTrace (prefixWord ++ tailWord_53756) baseStart_53756 baseEnd_53756 := by
    simpa [prefixWord, tailWord_53756, baseEnd_53756] using wordTrace_append hprefix tailTrace_53756
  have hstable : (prefixWord ++ tailWord_53756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53756).length < 2 ^ (prefixWord ++ tailWord_53756).sum := by decide
  have hdescent : baseEnd_53756 < baseStart_53756 := by decide
  rcases family_descends (prefixWord ++ tailWord_53756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53771 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_53771 : Nat := 118140960795 + 53771 * 2 ^ 59
def prefixEnd_53771 : Nat := 4983230072969 + 3 ^ 40 * 53771 * 2
def baseEnd_53771 : Nat := 18406912182009569610145

theorem tailTrace_53771 : CollatzResearch.WordTrace tailWord_53771 prefixEnd_53771 18406912182009569610145 := by
  unfold tailWord_53771
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961189488204325200785167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1307459658802883467190111 1961189488204325200785167)
  ·
    refine ⟨2941784232306487801177751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1961189488204325200785167 2941784232306487801177751)
    ·
      refine ⟨4412676348459731701766627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941784232306487801177751 4412676348459731701766627)
      ·
        refine ⟨6619014522689597552649941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412676348459731701766627 6619014522689597552649941)
        ·
          refine ⟨155133152875537442640233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6619014522689597552649941 155133152875537442640233)
          ·
            refine ⟨116349864656653081980175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155133152875537442640233 116349864656653081980175)
            ·
              refine ⟨174524796984979622970263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116349864656653081980175 174524796984979622970263)
              ·
                refine ⟨261787195477469434455395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174524796984979622970263 261787195477469434455395)
                ·
                  refine ⟨392680793216204151683093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261787195477469434455395 392680793216204151683093)
                  ·
                    refine ⟨18406912182009569610145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 392680793216204151683093 18406912182009569610145)
                    ·
                      rfl

theorem cell22_53771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_53771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53771 prefixEnd_53771 := by exact prefixLift 53771
  have htrace : WordTrace (prefixWord ++ tailWord_53771) baseStart_53771 baseEnd_53771 := by
    simpa [prefixWord, tailWord_53771, baseEnd_53771] using wordTrace_append hprefix tailTrace_53771
  have hstable : (prefixWord ++ tailWord_53771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53771).length < 2 ^ (prefixWord ++ tailWord_53771).sum := by decide
  have hdescent : baseEnd_53771 < baseStart_53771 := by decide
  rcases family_descends (prefixWord ++ tailWord_53771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53818 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_53818 : Nat := 118140960795 + 53818 * 2 ^ 59
def prefixEnd_53818 : Nat := 4983230072969 + 3 ^ 40 * 53818 * 2
def baseEnd_53818 : Nat := 18423001242517113685001

theorem tailTrace_53818 : CollatzResearch.WordTrace tailWord_53818 prefixEnd_53818 18423001242517113685001 := by
  unfold tailWord_53818
  simp only [CollatzResearch.WordTrace]
  refine ⟨490725929758513056936527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1308602479356034818497405 490725929758513056936527)
  ·
    refine ⟨736088894637769585404791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490725929758513056936527 736088894637769585404791)
    ·
      refine ⟨1104133341956654378107187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736088894637769585404791 1104133341956654378107187)
      ·
        refine ⟨1656200012934981567160781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104133341956654378107187 1656200012934981567160781)
        ·
          refine ⟨621075004850618087685293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1656200012934981567160781 621075004850618087685293)
          ·
            refine ⟨232903126818981782881985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621075004850618087685293 232903126818981782881985)
            ·
              refine ⟨174677345114236337161489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232903126818981782881985 174677345114236337161489)
              ·
                refine ⟨131008008835677252871117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174677345114236337161489 131008008835677252871117)
                ·
                  refine ⟨49128003313378969826669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131008008835677252871117 49128003313378969826669)
                  ·
                    refine ⟨18423001242517113685001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49128003313378969826669 18423001242517113685001)
                    ·
                      rfl

theorem cell22_53818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_53818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53818 prefixEnd_53818 := by exact prefixLift 53818
  have htrace : WordTrace (prefixWord ++ tailWord_53818) baseStart_53818 baseEnd_53818 := by
    simpa [prefixWord, tailWord_53818, baseEnd_53818] using wordTrace_append hprefix tailTrace_53818
  have hstable : (prefixWord ++ tailWord_53818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53818).length < 2 ^ (prefixWord ++ tailWord_53818).sum := by decide
  have hdescent : baseEnd_53818 < baseStart_53818 := by decide
  rcases family_descends (prefixWord ++ tailWord_53818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53831 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 7]
def baseStart_53831 : Nat := 118140960795 + 53831 * 2 ^ 59
def prefixEnd_53831 : Nat := 4983230072969 + 3 ^ 40 * 53831 * 2
def baseEnd_53831 : Nat := 6142483802729804369987

theorem tailTrace_53831 : CollatzResearch.WordTrace tailWord_53831 prefixEnd_53831 6142483802729804369987 := by
  unfold tailWord_53831
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963377867986955447969347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1308918578657970298646231 1963377867986955447969347)
  ·
    refine ⟨2945066801980433171954021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963377867986955447969347 2945066801980433171954021)
    ·
      refine ⟨552200025371331219741379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2945066801980433171954021 552200025371331219741379)
      ·
        refine ⟨828300038056996829612069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552200025371331219741379 828300038056996829612069)
        ·
          refine ⟨155306257135686905552263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 828300038056996829612069 155306257135686905552263)
          ·
            refine ⟨232959385703530358328395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155306257135686905552263 232959385703530358328395)
            ·
              refine ⟨349439078555295537492593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232959385703530358328395 349439078555295537492593)
              ·
                refine ⟨262079308916471653119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349439078555295537492593 262079308916471653119445)
                ·
                  refine ⟨6142483802729804369987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 262079308916471653119445 6142483802729804369987)
                  ·
                    rfl

theorem cell22_53831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_53831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53831 prefixEnd_53831 := by exact prefixLift 53831
  have htrace : WordTrace (prefixWord ++ tailWord_53831) baseStart_53831 baseEnd_53831 := by
    simpa [prefixWord, tailWord_53831, baseEnd_53831] using wordTrace_append hprefix tailTrace_53831
  have hstable : (prefixWord ++ tailWord_53831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53831).length < 2 ^ (prefixWord ++ tailWord_53831).sum := by decide
  have hdescent : baseEnd_53831 < baseStart_53831 := by decide
  rcases family_descends (prefixWord ++ tailWord_53831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53835 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 1, 3]
def baseStart_53835 : Nat := 118140960795 + 53835 * 2 ^ 59
def prefixEnd_53835 : Nat := 4983230072969 + 3 ^ 40 * 53835 * 2
def baseEnd_53835 : Nat := 18428820689934736009949

theorem tailTrace_53835 : CollatzResearch.WordTrace tailWord_53835 prefixEnd_53835 18428820689934736009949 := by
  unfold tailWord_53835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963523759972464131114959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309015839981642754076639 1963523759972464131114959)
  ·
    refine ⟨2945285639958696196672439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963523759972464131114959 2945285639958696196672439)
    ·
      refine ⟨4417928459938044295008659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945285639958696196672439 4417928459938044295008659)
      ·
        refine ⟨6626892689907066442512989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417928459938044295008659 6626892689907066442512989)
        ·
          refine ⟨2485084758715149915942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6626892689907066442512989 2485084758715149915942371)
          ·
            refine ⟨3727627138072724873913557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485084758715149915942371 3727627138072724873913557)
            ·
              refine ⟨87366261048579489232349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3727627138072724873913557 87366261048579489232349)
              ·
                refine ⟨32762347893217308462131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87366261048579489232349 32762347893217308462131)
                ·
                  refine ⟨49143521839825962693197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32762347893217308462131 49143521839825962693197)
                  ·
                    refine ⟨18428820689934736009949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49143521839825962693197 18428820689934736009949)
                    ·
                      rfl

theorem cell22_53835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 3].length) (baseStart_53835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53835 prefixEnd_53835 := by exact prefixLift 53835
  have htrace : WordTrace (prefixWord ++ tailWord_53835) baseStart_53835 baseEnd_53835 := by
    simpa [prefixWord, tailWord_53835, baseEnd_53835] using wordTrace_append hprefix tailTrace_53835
  have hstable : (prefixWord ++ tailWord_53835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53835).length < 2 ^ (prefixWord ++ tailWord_53835).sum := by decide
  have hdescent : baseEnd_53835 < baseStart_53835 := by decide
  rcases family_descends (prefixWord ++ tailWord_53835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53852 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_53852 : Nat := 118140960795 + 53852 * 2 ^ 59
def prefixEnd_53852 : Nat := 4983230072969 + 3 ^ 40 * 53852 * 2
def baseEnd_53852 : Nat := 18434640137352358334897

theorem tailTrace_53852 : CollatzResearch.WordTrace tailWord_53852 prefixEnd_53852 18434640137352358334897 := by
  unfold tailWord_53852
  simp only [CollatzResearch.WordTrace]
  refine ⟨982071900455438017241905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1309429200607250689655873 982071900455438017241905)
  ·
    refine ⟨736553925341578512931429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 982071900455438017241905 736553925341578512931429)
    ·
      refine ⟨138103861001545971174643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 736553925341578512931429 138103861001545971174643)
      ·
        refine ⟨207155791502318956761965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138103861001545971174643 207155791502318956761965)
        ·
          refine ⟨77683421813369608785737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207155791502318956761965 77683421813369608785737)
          ·
            refine ⟨58262566360027206589303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77683421813369608785737 58262566360027206589303)
            ·
              refine ⟨87393849540040809883955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58262566360027206589303 87393849540040809883955)
              ·
                refine ⟨131090774310061214825933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87393849540040809883955 131090774310061214825933)
                ·
                  refine ⟨49159040366272955559725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131090774310061214825933 49159040366272955559725)
                  ·
                    refine ⟨18434640137352358334897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49159040366272955559725 18434640137352358334897)
                    ·
                      rfl

theorem cell22_53852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_53852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53852 prefixEnd_53852 := by exact prefixLift 53852
  have htrace : WordTrace (prefixWord ++ tailWord_53852) baseStart_53852 baseEnd_53852 := by
    simpa [prefixWord, tailWord_53852, baseEnd_53852] using wordTrace_append hprefix tailTrace_53852
  have hstable : (prefixWord ++ tailWord_53852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53852).length < 2 ^ (prefixWord ++ tailWord_53852).sum := by decide
  have hdescent : baseEnd_53852 < baseStart_53852 := by decide
  rcases family_descends (prefixWord ++ tailWord_53852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53891 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_53891 : Nat := 118140960795 + 53891 * 2 ^ 59
def prefixEnd_53891 : Nat := 4983230072969 + 3 ^ 40 * 53891 * 2
def baseEnd_53891 : Nat := 18447990634369256609777

theorem tailTrace_53891 : CollatzResearch.WordTrace tailWord_53891 prefixEnd_53891 18447990634369256609777 := by
  unfold tailWord_53891
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965566247769585695153527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1310377498513057130102351 1965566247769585695153527)
  ·
    refine ⟨2948349371654378542730291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965566247769585695153527 2948349371654378542730291)
    ·
      refine ⟨4422524057481567814095437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948349371654378542730291 4422524057481567814095437)
      ·
        refine ⟨1658446521555587930285789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4422524057481567814095437 1658446521555587930285789)
        ·
          refine ⟨621917445583345473857171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1658446521555587930285789 621917445583345473857171)
          ·
            refine ⟨932876168375018210785757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621917445583345473857171 932876168375018210785757)
            ·
              refine ⟨349828563140631829044659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932876168375018210785757 349828563140631829044659)
              ·
                refine ⟨524742844710947743566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349828563140631829044659 524742844710947743566989)
                ·
                  refine ⟨196778566766605403837621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524742844710947743566989 196778566766605403837621)
                  ·
                    refine ⟨18447990634369256609777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196778566766605403837621 18447990634369256609777)
                    ·
                      rfl

theorem cell22_53891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_53891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53891 prefixEnd_53891 := by exact prefixLift 53891
  have htrace : WordTrace (prefixWord ++ tailWord_53891) baseStart_53891 baseEnd_53891 := by
    simpa [prefixWord, tailWord_53891, baseEnd_53891] using wordTrace_append hprefix tailTrace_53891
  have hstable : (prefixWord ++ tailWord_53891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53891).length < 2 ^ (prefixWord ++ tailWord_53891).sum := by decide
  have hdescent : baseEnd_53891 < baseStart_53891 := by decide
  rcases family_descends (prefixWord ++ tailWord_53891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53895 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 1, 4]
def baseStart_53895 : Nat := 118140960795 + 53895 * 2 ^ 59
def prefixEnd_53895 : Nat := 4983230072969 + 3 ^ 40 * 53895 * 2
def baseEnd_53895 : Nat := 18449359916114579509765

theorem tailTrace_53895 : CollatzResearch.WordTrace tailWord_53895 prefixEnd_53895 18449359916114579509765 := by
  unfold tailWord_53895
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965712139755094378299139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1310474759836729585532759 1965712139755094378299139)
  ·
    refine ⟨2948568209632641567448709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965712139755094378299139 2948568209632641567448709)
    ·
      refine ⟨552856539306120293896633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2948568209632641567448709 552856539306120293896633)
      ·
        refine ⟨414642404479590220422475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552856539306120293896633 414642404479590220422475)
        ·
          refine ⟨621963606719385330633713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414642404479590220422475 621963606719385330633713)
          ·
            refine ⟨466472705039538997975285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621963606719385330633713 466472705039538997975285)
            ·
              refine ⟨43731816097456781060183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466472705039538997975285 43731816097456781060183)
              ·
                refine ⟨65597724146185171590275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43731816097456781060183 65597724146185171590275)
                ·
                  refine ⟨98396586219277757385413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65597724146185171590275 98396586219277757385413)
                  ·
                    refine ⟨18449359916114579509765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98396586219277757385413 18449359916114579509765)
                    ·
                      rfl

theorem cell22_53895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_53895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53895 prefixEnd_53895 := by exact prefixLift 53895
  have htrace : WordTrace (prefixWord ++ tailWord_53895) baseStart_53895 baseEnd_53895 := by
    simpa [prefixWord, tailWord_53895, baseEnd_53895] using wordTrace_append hprefix tailTrace_53895
  have hstable : (prefixWord ++ tailWord_53895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53895).length < 2 ^ (prefixWord ++ tailWord_53895).sum := by decide
  have hdescent : baseEnd_53895 < baseStart_53895 := by decide
  rcases family_descends (prefixWord ++ tailWord_53895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54047 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 1, 4]
def baseStart_54047 : Nat := 118140960795 + 54047 * 2 ^ 59
def prefixEnd_54047 : Nat := 4983230072969 + 3 ^ 40 * 54047 * 2
def baseEnd_54047 : Nat := 18501392622436849709299

theorem tailTrace_54047 : CollatzResearch.WordTrace tailWord_54047 prefixEnd_54047 18501392622436849709299 := by
  unfold tailWord_54047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971256035204424337832395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1314170690136282891888263 1971256035204424337832395)
  ·
    refine ⟨2956884052806636506748593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1971256035204424337832395 2956884052806636506748593)
    ·
      refine ⟨2217663039604977380061445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956884052806636506748593 2217663039604977380061445)
      ·
        refine ⟨415811819925933258761521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2217663039604977380061445 415811819925933258761521)
        ·
          refine ⟨311858864944449944071141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415811819925933258761521 311858864944449944071141)
          ·
            refine ⟨58473537177084364513339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311858864944449944071141 58473537177084364513339)
            ·
              refine ⟨87710305765626546770009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58473537177084364513339 87710305765626546770009)
              ·
                refine ⟨65782729324219910077507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87710305765626546770009 65782729324219910077507)
                ·
                  refine ⟨98674093986329865116261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65782729324219910077507 98674093986329865116261)
                  ·
                    refine ⟨18501392622436849709299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98674093986329865116261 18501392622436849709299)
                    ·
                      rfl

theorem cell22_54047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_54047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54047 prefixEnd_54047 := by exact prefixLift 54047
  have htrace : WordTrace (prefixWord ++ tailWord_54047) baseStart_54047 baseEnd_54047 := by
    simpa [prefixWord, tailWord_54047, baseEnd_54047] using wordTrace_append hprefix tailTrace_54047
  have hstable : (prefixWord ++ tailWord_54047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54047).length < 2 ^ (prefixWord ++ tailWord_54047).sum := by decide
  have hdescent : baseEnd_54047 < baseStart_54047 := by decide
  rcases family_descends (prefixWord ++ tailWord_54047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54079 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 4]
def baseStart_54079 : Nat := 118140960795 + 54079 * 2 ^ 59
def prefixEnd_54079 : Nat := 4983230072969 + 3 ^ 40 * 54079 * 2
def baseEnd_54079 : Nat := 6170782292133144303067

theorem tailTrace_54079 : CollatzResearch.WordTrace tailWord_54079 prefixEnd_54079 6170782292133144303067 := by
  unfold tailWord_54079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972423171088493802997291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1314948780725662535331527 1972423171088493802997291)
  ·
    refine ⟨2958634756632740704495937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972423171088493802997291 2958634756632740704495937)
    ·
      refine ⟨2218976067474555528371953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2958634756632740704495937 2218976067474555528371953)
      ·
        refine ⟨1664232050605916646278965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2218976067474555528371953 1664232050605916646278965)
        ·
          refine ⟨156021754744304685588653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1664232050605916646278965 156021754744304685588653)
          ·
            refine ⟨58508158029114257095745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156021754744304685588653 58508158029114257095745)
            ·
              refine ⟨43881118521835692821809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58508158029114257095745 43881118521835692821809)
              ·
                refine ⟨32910838891376769616357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43881118521835692821809 32910838891376769616357)
                ·
                  refine ⟨6170782292133144303067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32910838891376769616357 6170782292133144303067)
                  ·
                    rfl

theorem cell22_54079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 4].length) (baseStart_54079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54079 prefixEnd_54079 := by exact prefixLift 54079
  have htrace : WordTrace (prefixWord ++ tailWord_54079) baseStart_54079 baseEnd_54079 := by
    simpa [prefixWord, tailWord_54079, baseEnd_54079] using wordTrace_append hprefix tailTrace_54079
  have hstable : (prefixWord ++ tailWord_54079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54079).length < 2 ^ (prefixWord ++ tailWord_54079).sum := by decide
  have hdescent : baseEnd_54079 < baseStart_54079 := by decide
  rcases family_descends (prefixWord ++ tailWord_54079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54105 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_54105 : Nat := 118140960795 + 54105 * 2 ^ 59
def prefixEnd_54105 : Nat := 4983230072969 + 3 ^ 40 * 54105 * 2
def baseEnd_54105 : Nat := 18521247207744031759121

theorem tailTrace_54105 : CollatzResearch.WordTrace tailWord_54105 prefixEnd_54105 18521247207744031759121 := by
  unfold tailWord_54105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973371468994300243443769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1315580979329533495629179 1973371468994300243443769)
  ·
    refine ⟨1480028601745725182582827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973371468994300243443769 1480028601745725182582827)
    ·
      refine ⟨2220042902618587773874241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480028601745725182582827 2220042902618587773874241)
      ·
        refine ⟨1665032176963940830405681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220042902618587773874241 1665032176963940830405681)
        ·
          refine ⟨1248774132722955622804261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665032176963940830405681 1248774132722955622804261)
          ·
            refine ⟨234145149885554179275799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1248774132722955622804261 234145149885554179275799)
            ·
              refine ⟨351217724828331268913699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234145149885554179275799 351217724828331268913699)
              ·
                refine ⟨526826587242496903370549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351217724828331268913699 526826587242496903370549)
                ·
                  refine ⟨49389992553984084690989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526826587242496903370549 49389992553984084690989)
                  ·
                    refine ⟨18521247207744031759121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49389992553984084690989 18521247207744031759121)
                    ·
                      rfl

theorem cell22_54105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_54105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54105 prefixEnd_54105 := by exact prefixLift 54105
  have htrace : WordTrace (prefixWord ++ tailWord_54105) baseStart_54105 baseEnd_54105 := by
    simpa [prefixWord, tailWord_54105, baseEnd_54105] using wordTrace_append hprefix tailTrace_54105
  have hstable : (prefixWord ++ tailWord_54105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54105).length < 2 ^ (prefixWord ++ tailWord_54105).sum := by decide
  have hdescent : baseEnd_54105 < baseStart_54105 := by decide
  rcases family_descends (prefixWord ++ tailWord_54105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54163 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 8]
def baseStart_54163 : Nat := 118140960795 + 54163 * 2 ^ 59
def prefixEnd_54163 : Nat := 4983230072969 + 3 ^ 40 * 54163 * 2
def baseEnd_54163 : Nat := 6180367264350404602981

theorem tailTrace_54163 : CollatzResearch.WordTrace tailWord_54163 prefixEnd_54163 6180367264350404602981 := by
  unfold tailWord_54163
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975486902784176149055143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1316991268522784099370095 1975486902784176149055143)
  ·
    refine ⟨2963230354176264223582715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975486902784176149055143 2963230354176264223582715)
    ·
      refine ⟨4444845531264396335374073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963230354176264223582715 4444845531264396335374073)
      ·
        refine ⟨3333634148448297251530555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444845531264396335374073 3333634148448297251530555)
        ·
          refine ⟨5000451222672445877295833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333634148448297251530555 5000451222672445877295833)
          ·
            refine ⟨3750338417004334407971875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000451222672445877295833 3750338417004334407971875)
            ·
              refine ⟨5625507625506501611957813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750338417004334407971875 5625507625506501611957813)
              ·
                refine ⟨527391339891234526121045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5625507625506501611957813 527391339891234526121045)
                ·
                  refine ⟨6180367264350404602981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 527391339891234526121045 6180367264350404602981)
                  ·
                    rfl

theorem cell22_54163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_54163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54163 prefixEnd_54163 := by exact prefixLift 54163
  have htrace : WordTrace (prefixWord ++ tailWord_54163) baseStart_54163 baseEnd_54163 := by
    simpa [prefixWord, tailWord_54163, baseEnd_54163] using wordTrace_append hprefix tailTrace_54163
  have hstable : (prefixWord ++ tailWord_54163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54163).length < 2 ^ (prefixWord ++ tailWord_54163).sum := by decide
  have hdescent : baseEnd_54163 < baseStart_54163 := by decide
  rcases family_descends (prefixWord ++ tailWord_54163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54216 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_54216 : Nat := 118140960795 + 54216 * 2 ^ 59
def prefixEnd_54216 : Nat := 4983230072969 + 3 ^ 40 * 54216 * 2
def baseEnd_54216 : Nat := 18559244776176742233781

theorem tailTrace_54216 : CollatzResearch.WordTrace tailWord_54216 prefixEnd_54216 18559244776176742233781 := by
  unfold tailWord_54216
  simp only [CollatzResearch.WordTrace]
  refine ⟨988709985796083100367251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1318279981061444133823001 988709985796083100367251)
  ·
    refine ⟨1483064978694124650550877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988709985796083100367251 1483064978694124650550877)
    ·
      refine ⟨556149367010296743956579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1483064978694124650550877 556149367010296743956579)
      ·
        refine ⟨834224050515445115934869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556149367010296743956579 834224050515445115934869)
        ·
          refine ⟨39104252367911489809447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 834224050515445115934869 39104252367911489809447)
          ·
            refine ⟨58656378551867234714171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39104252367911489809447 58656378551867234714171)
            ·
              refine ⟨87984567827800852071257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58656378551867234714171 87984567827800852071257)
              ·
                refine ⟨65988425870850639053443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87984567827800852071257 65988425870850639053443)
                ·
                  refine ⟨98982638806275958580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65988425870850639053443 98982638806275958580165)
                  ·
                    refine ⟨18559244776176742233781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98982638806275958580165 18559244776176742233781)
                    ·
                      rfl

theorem cell22_54216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_54216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54216 prefixEnd_54216 := by exact prefixLift 54216
  have htrace : WordTrace (prefixWord ++ tailWord_54216) baseStart_54216 baseEnd_54216 := by
    simpa [prefixWord, tailWord_54216, baseEnd_54216] using wordTrace_append hprefix tailTrace_54216
  have hstable : (prefixWord ++ tailWord_54216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54216).length < 2 ^ (prefixWord ++ tailWord_54216).sum := by decide
  have hdescent : baseEnd_54216 < baseStart_54216 := by decide
  rcases family_descends (prefixWord ++ tailWord_54216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54242 : List Nat := [3, 3, 3, 1, 1, 11]
def baseStart_54242 : Nat := 118140960795 + 54242 * 2 ^ 59
def prefixEnd_54242 : Nat := 4983230072969 + 3 ^ 40 * 54242 * 2
def baseEnd_54242 : Nat := 229236359352115322021

theorem tailTrace_54242 : CollatzResearch.WordTrace tailWord_54242 prefixEnd_54242 229236359352115322021 := by
  unfold tailWord_54242
  simp only [CollatzResearch.WordTrace]
  refine ⟨494592067374493160295245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1318912179665315094120653 494592067374493160295245)
  ·
    refine ⟨185472025265434935110717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 494592067374493160295245 185472025265434935110717)
    ·
      refine ⟨69552009474538100666519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185472025265434935110717 69552009474538100666519)
      ·
        refine ⟨104328014211807150999779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69552009474538100666519 104328014211807150999779)
        ·
          refine ⟨156492021317710726499669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104328014211807150999779 156492021317710726499669)
          ·
            refine ⟨229236359352115322021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 156492021317710726499669 229236359352115322021)
            ·
              rfl

theorem cell22_54242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 11].length) (baseStart_54242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54242 prefixEnd_54242 := by exact prefixLift 54242
  have htrace : WordTrace (prefixWord ++ tailWord_54242) baseStart_54242 baseEnd_54242 := by
    simpa [prefixWord, tailWord_54242, baseEnd_54242] using wordTrace_append hprefix tailTrace_54242
  have hstable : (prefixWord ++ tailWord_54242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54242).length < 2 ^ (prefixWord ++ tailWord_54242).sum := by decide
  have hdescent : baseEnd_54242 < baseStart_54242 := by decide
  rcases family_descends (prefixWord ++ tailWord_54242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54255 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_54255 : Nat := 118140960795 + 54255 * 2 ^ 59
def prefixEnd_54255 : Nat := 4983230072969 + 3 ^ 40 * 54255 * 2
def baseEnd_54255 : Nat := 18572595273193640508661

theorem tailTrace_54255 : CollatzResearch.WordTrace tailWord_54255 prefixEnd_54255 18572595273193640508661 := by
  unfold tailWord_54255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978842418450875861404219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1319228278967250574269479 1978842418450875861404219)
  ·
    refine ⟨2968263627676313792106329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978842418450875861404219 2968263627676313792106329)
    ·
      refine ⟨2226197720757235344079747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968263627676313792106329 2226197720757235344079747)
      ·
        refine ⟨3339296581135853016119621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226197720757235344079747 3339296581135853016119621)
        ·
          refine ⟨626118108962972440522429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3339296581135853016119621 626118108962972440522429)
          ·
            refine ⟨234794290861114665195911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626118108962972440522429 234794290861114665195911)
            ·
              refine ⟨352191436291671997793867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234794290861114665195911 352191436291671997793867)
              ·
                refine ⟨528287154437507996690801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352191436291671997793867 528287154437507996690801)
                ·
                  refine ⟨396215365828130997518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528287154437507996690801 396215365828130997518101)
                  ·
                    refine ⟨18572595273193640508661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 396215365828130997518101 18572595273193640508661)
                    ·
                      rfl

theorem cell22_54255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_54255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54255 prefixEnd_54255 := by exact prefixLift 54255
  have htrace : WordTrace (prefixWord ++ tailWord_54255) baseStart_54255 baseEnd_54255 := by
    simpa [prefixWord, tailWord_54255, baseEnd_54255] using wordTrace_append hprefix tailTrace_54255
  have hstable : (prefixWord ++ tailWord_54255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54255).length < 2 ^ (prefixWord ++ tailWord_54255).sum := by decide
  have hdescent : baseEnd_54255 < baseStart_54255 := by decide
  rcases family_descends (prefixWord ++ tailWord_54255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54304 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_54304 : Nat := 118140960795 + 54304 * 2 ^ 59
def prefixEnd_54304 : Nat := 4983230072969 + 3 ^ 40 * 54304 * 2
def baseEnd_54304 : Nat := 6196456324857948677837

theorem tailTrace_54304 : CollatzResearch.WordTrace tailWord_54304 prefixEnd_54304 6196456324857948677837 := by
  unfold tailWord_54304
  simp only [CollatzResearch.WordTrace]
  refine ⟨990314797636678614968983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1320419730182238153291977 990314797636678614968983)
  ·
    refine ⟨1485472196455017922453475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990314797636678614968983 1485472196455017922453475)
    ·
      refine ⟨2228208294682526883680213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485472196455017922453475 2228208294682526883680213)
      ·
        refine ⟨52223631906621723836255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2228208294682526883680213 52223631906621723836255)
        ·
          refine ⟨78335447859932585754383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52223631906621723836255 78335447859932585754383)
          ·
            refine ⟨117503171789898878631575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78335447859932585754383 117503171789898878631575)
            ·
              refine ⟨176254757684848317947363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117503171789898878631575 176254757684848317947363)
              ·
                refine ⟨264382136527272476921045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176254757684848317947363 264382136527272476921045)
                ·
                  refine ⟨6196456324857948677837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 264382136527272476921045 6196456324857948677837)
                  ·
                    rfl

theorem cell22_54304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_54304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54304 prefixEnd_54304 := by exact prefixLift 54304
  have htrace : WordTrace (prefixWord ++ tailWord_54304) baseStart_54304 baseEnd_54304 := by
    simpa [prefixWord, tailWord_54304, baseEnd_54304] using wordTrace_append hprefix tailTrace_54304
  have hstable : (prefixWord ++ tailWord_54304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54304).length < 2 ^ (prefixWord ++ tailWord_54304).sum := by decide
  have hdescent : baseEnd_54304 < baseStart_54304 := by decide
  rcases family_descends (prefixWord ++ tailWord_54304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54332 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_54332 : Nat := 118140960795 + 54332 * 2 ^ 59
def prefixEnd_54332 : Nat := 4983230072969 + 3 ^ 40 * 54332 * 2
def baseEnd_54332 : Nat := 6199651315597035444475

theorem tailTrace_54332 : CollatzResearch.WordTrace tailWord_54332 prefixEnd_54332 6199651315597035444475 := by
  unfold tailWord_54332
  simp only [CollatzResearch.WordTrace]
  refine ⟨990825419585959005978625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1321100559447945341304833 990825419585959005978625)
  ·
    refine ⟨743119064689469254483969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 990825419585959005978625 743119064689469254483969)
    ·
      refine ⟨557339298517101940862977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743119064689469254483969 557339298517101940862977)
      ·
        refine ⟨418004473887826455647233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557339298517101940862977 418004473887826455647233)
        ·
          refine ⟨313503355415869841735425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418004473887826455647233 313503355415869841735425)
          ·
            refine ⟨235127516561902381301569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313503355415869841735425 235127516561902381301569)
            ·
              refine ⟨176345637421426785976177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235127516561902381301569 176345637421426785976177)
              ·
                refine ⟨132259228066070089482133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176345637421426785976177 132259228066070089482133)
                ·
                  refine ⟨6199651315597035444475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132259228066070089482133 6199651315597035444475)
                  ·
                    rfl

theorem cell22_54332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_54332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54332 prefixEnd_54332 := by exact prefixLift 54332
  have htrace : WordTrace (prefixWord ++ tailWord_54332) baseStart_54332 baseEnd_54332 := by
    simpa [prefixWord, tailWord_54332, baseEnd_54332] using wordTrace_append hprefix tailTrace_54332
  have hstable : (prefixWord ++ tailWord_54332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54332).length < 2 ^ (prefixWord ++ tailWord_54332).sum := by decide
  have hdescent : baseEnd_54332 < baseStart_54332 := by decide
  rcases family_descends (prefixWord ++ tailWord_54332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54364 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_54364 : Nat := 118140960795 + 54364 * 2 ^ 59
def prefixEnd_54364 : Nat := 4983230072969 + 3 ^ 40 * 54364 * 2
def baseEnd_54364 : Nat := 18609908200753689533327

theorem tailTrace_54364 : CollatzResearch.WordTrace tailWord_54364 prefixEnd_54364 18609908200753689533327 := by
  unfold tailWord_54364
  simp only [CollatzResearch.WordTrace]
  refine ⟨991408987527993738561073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1321878650037324984748097 991408987527993738561073)
  ·
    refine ⟨743556740645995303920805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 991408987527993738561073 743556740645995303920805)
    ·
      refine ⟨139416888871124119485151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 743556740645995303920805 139416888871124119485151)
      ·
        refine ⟨209125333306686179227727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139416888871124119485151 209125333306686179227727)
        ·
          refine ⟨313687999960029268841591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209125333306686179227727 313687999960029268841591)
          ·
            refine ⟨470531999940043903262387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313687999960029268841591 470531999940043903262387)
            ·
              refine ⟨705797999910065854893581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470531999940043903262387 705797999910065854893581)
              ·
                refine ⟨264674249966274695585093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705797999910065854893581 264674249966274695585093)
                ·
                  refine ⟨49626421868676505422205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264674249966274695585093 49626421868676505422205)
                  ·
                    refine ⟨18609908200753689533327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49626421868676505422205 18609908200753689533327)
                    ·
                      rfl

theorem cell22_54364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_54364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54364 prefixEnd_54364 := by exact prefixLift 54364
  have htrace : WordTrace (prefixWord ++ tailWord_54364) baseStart_54364 baseEnd_54364 := by
    simpa [prefixWord, tailWord_54364, baseEnd_54364] using wordTrace_append hprefix tailTrace_54364
  have hstable : (prefixWord ++ tailWord_54364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54364).length < 2 ^ (prefixWord ++ tailWord_54364).sum := by decide
  have hdescent : baseEnd_54364 < baseStart_54364 := by decide
  rcases family_descends (prefixWord ++ tailWord_54364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54377 : List Nat := [1, 2, 1, 1, 1, 7, 2, 7]
def baseStart_54377 : Nat := 118140960795 + 54377 * 2 ^ 59
def prefixEnd_54377 : Nat := 4983230072969 + 3 ^ 40 * 54377 * 2
def baseEnd_54377 : Nat := 2068262040713998773143

theorem tailTrace_54377 : CollatzResearch.WordTrace tailWord_54377 prefixEnd_54377 2068262040713998773143 := by
  unfold tailWord_54377
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983292124008890697345385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1322194749339260464896923 1983292124008890697345385)
  ·
    refine ⟨1487469093006668023009039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1983292124008890697345385 1487469093006668023009039)
    ·
      refine ⟨2231203639510002034513559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487469093006668023009039 2231203639510002034513559)
      ·
        refine ⟨3346805459265003051770339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231203639510002034513559 3346805459265003051770339)
        ·
          refine ⟨5020208188897504577655509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346805459265003051770339 5020208188897504577655509)
          ·
            refine ⟨117661129427285263538801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5020208188897504577655509 117661129427285263538801)
            ·
              refine ⟨88245847070463947654101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117661129427285263538801 88245847070463947654101)
              ·
                refine ⟨2068262040713998773143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88245847070463947654101 2068262040713998773143)
                ·
                  rfl

theorem cell22_54377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 7].length) (baseStart_54377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54377 prefixEnd_54377 := by exact prefixLift 54377
  have htrace : WordTrace (prefixWord ++ tailWord_54377) baseStart_54377 baseEnd_54377 := by
    simpa [prefixWord, tailWord_54377, baseEnd_54377] using wordTrace_append hprefix tailTrace_54377
  have hstable : (prefixWord ++ tailWord_54377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54377).length < 2 ^ (prefixWord ++ tailWord_54377).sum := by decide
  have hdescent : baseEnd_54377 < baseStart_54377 := by decide
  rcases family_descends (prefixWord ++ tailWord_54377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54381 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_54381 : Nat := 118140960795 + 54381 * 2 ^ 59
def prefixEnd_54381 : Nat := 4983230072969 + 3 ^ 40 * 54381 * 2
def baseEnd_54381 : Nat := 18615727648171311858275

theorem tailTrace_54381 : CollatzResearch.WordTrace tailWord_54381 prefixEnd_54381 18615727648171311858275 := by
  unfold tailWord_54381
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983438015994399380490997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1322292010662932920327331 1983438015994399380490997)
  ·
    refine ⟨185947313999474941921031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1983438015994399380490997 185947313999474941921031)
    ·
      refine ⟨278920970999212412881547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185947313999474941921031 278920970999212412881547)
      ·
        refine ⟨418381456498818619322321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278920970999212412881547 418381456498818619322321)
        ·
          refine ⟨313786092374113964491741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418381456498818619322321 313786092374113964491741)
          ·
            refine ⟨117669784640292736684403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313786092374113964491741 117669784640292736684403)
            ·
              refine ⟨176504676960439105026605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117669784640292736684403 176504676960439105026605)
              ·
                refine ⟨66189253860164664384977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176504676960439105026605 66189253860164664384977)
                ·
                  refine ⟨49641940395123498288733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66189253860164664384977 49641940395123498288733)
                  ·
                    refine ⟨18615727648171311858275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49641940395123498288733 18615727648171311858275)
                    ·
                      rfl

theorem cell22_54381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_54381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54381 prefixEnd_54381 := by exact prefixLift 54381
  have htrace : WordTrace (prefixWord ++ tailWord_54381) baseStart_54381 baseEnd_54381 := by
    simpa [prefixWord, tailWord_54381, baseEnd_54381] using wordTrace_append hprefix tailTrace_54381
  have hstable : (prefixWord ++ tailWord_54381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54381).length < 2 ^ (prefixWord ++ tailWord_54381).sum := by decide
  have hdescent : baseEnd_54381 < baseStart_54381 := by decide
  rcases family_descends (prefixWord ++ tailWord_54381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54437 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_54437 : Nat := 118140960795 + 54437 * 2 ^ 59
def prefixEnd_54437 : Nat := 4983230072969 + 3 ^ 40 * 54437 * 2
def baseEnd_54437 : Nat := 18634897592605832458103

theorem tailTrace_54437 : CollatzResearch.WordTrace tailWord_54437 prefixEnd_54437 18634897592605832458103 := by
  unfold tailWord_54437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985480503791520944529565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1323653669194347296353043 1985480503791520944529565)
  ·
    refine ⟨744555188921820354198587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1985480503791520944529565 744555188921820354198587)
    ·
      refine ⟨1116832783382730531297881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744555188921820354198587 1116832783382730531297881)
      ·
        refine ⟨837624587537047898473411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116832783382730531297881 837624587537047898473411)
        ·
          refine ⟨1256436881305571847710117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837624587537047898473411 1256436881305571847710117)
          ·
            refine ⟨235581915244794721445647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1256436881305571847710117 235581915244794721445647)
            ·
              refine ⟨353372872867192082168471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235581915244794721445647 353372872867192082168471)
              ·
                refine ⟨530059309300788123252707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353372872867192082168471 530059309300788123252707)
                ·
                  refine ⟨795088963951182184879061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530059309300788123252707 795088963951182184879061)
                  ·
                    refine ⟨18634897592605832458103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 795088963951182184879061 18634897592605832458103)
                    ·
                      rfl

theorem cell22_54437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_54437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54437 prefixEnd_54437 := by exact prefixLift 54437
  have htrace : WordTrace (prefixWord ++ tailWord_54437) baseStart_54437 baseEnd_54437 := by
    simpa [prefixWord, tailWord_54437, baseEnd_54437] using wordTrace_append hprefix tailTrace_54437
  have hstable : (prefixWord ++ tailWord_54437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54437).length < 2 ^ (prefixWord ++ tailWord_54437).sum := by decide
  have hdescent : baseEnd_54437 < baseStart_54437 := by decide
  rcases family_descends (prefixWord ++ tailWord_54437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54503 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 1, 4]
def baseStart_54503 : Nat := 118140960795 + 54503 * 2 ^ 59
def prefixEnd_54503 : Nat := 4983230072969 + 3 ^ 40 * 54503 * 2
def baseEnd_54503 : Nat := 18657490741403660307901

theorem tailTrace_54503 : CollatzResearch.WordTrace tailWord_54503 prefixEnd_54503 18657490741403660307901 := by
  unfold tailWord_54503
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987887721552414216432163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325258481034942810954775 1987887721552414216432163)
  ·
    refine ⟨2981831582328621324648245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987887721552414216432163 2981831582328621324648245)
    ·
      refine ⟨279546710843308249185773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2981831582328621324648245 279546710843308249185773)
      ·
        refine ⟨104830016566240593444665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279546710843308249185773 104830016566240593444665)
        ·
          refine ⟨78622512424680445083499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104830016566240593444665 78622512424680445083499)
          ·
            refine ⟨117933768637020667625249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78622512424680445083499 117933768637020667625249)
            ·
              refine ⟨88450326477765500718937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117933768637020667625249 88450326477765500718937)
              ·
                refine ⟨66337744858324125539203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88450326477765500718937 66337744858324125539203)
                ·
                  refine ⟨99506617287486188308805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66337744858324125539203 99506617287486188308805)
                  ·
                    refine ⟨18657490741403660307901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99506617287486188308805 18657490741403660307901)
                    ·
                      rfl

theorem cell22_54503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_54503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54503 prefixEnd_54503 := by exact prefixLift 54503
  have htrace : WordTrace (prefixWord ++ tailWord_54503) baseStart_54503 baseEnd_54503 := by
    simpa [prefixWord, tailWord_54503, baseEnd_54503] using wordTrace_append hprefix tailTrace_54503
  have hstable : (prefixWord ++ tailWord_54503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54503).length < 2 ^ (prefixWord ++ tailWord_54503).sum := by decide
  have hdescent : baseEnd_54503 < baseStart_54503 := by decide
  rcases family_descends (prefixWord ++ tailWord_54503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54529 : List Nat := [1, 2, 4, 1, 1, 5, 8]
def baseStart_54529 : Nat := 118140960795 + 54529 * 2 ^ 59
def prefixEnd_54529 : Nat := 4983230072969 + 3 ^ 40 * 54529 * 2
def baseEnd_54529 : Nat := 691347817509194783623

theorem tailTrace_54529 : CollatzResearch.WordTrace tailWord_54529 prefixEnd_54529 691347817509194783623 := by
  unfold tailWord_54529
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988836019458220656878641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325890679638813771252427 1988836019458220656878641)
  ·
    refine ⟨1491627014593665492658981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1988836019458220656878641 1491627014593665492658981)
    ·
      refine ⟨279680065236312279873559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1491627014593665492658981 279680065236312279873559)
      ·
        refine ⟨419520097854468419810339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279680065236312279873559 419520097854468419810339)
        ·
          refine ⟨629280146781702629715509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419520097854468419810339 629280146781702629715509)
          ·
            refine ⟨58995013760784621535829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 629280146781702629715509 58995013760784621535829)
            ·
              refine ⟨691347817509194783623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58995013760784621535829 691347817509194783623)
              ·
                rfl

theorem cell22_54529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 8].length) (baseStart_54529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54529 prefixEnd_54529 := by exact prefixLift 54529
  have htrace : WordTrace (prefixWord ++ tailWord_54529) baseStart_54529 baseEnd_54529 := by
    simpa [prefixWord, tailWord_54529, baseEnd_54529] using wordTrace_append hprefix tailTrace_54529
  have hstable : (prefixWord ++ tailWord_54529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54529).length < 2 ^ (prefixWord ++ tailWord_54529).sum := by decide
  have hdescent : baseEnd_54529 < baseStart_54529 := by decide
  rcases family_descends (prefixWord ++ tailWord_54529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54591 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 5]
def baseStart_54591 : Nat := 118140960795 + 54591 * 2 ^ 59
def prefixEnd_54591 : Nat := 4983230072969 + 3 ^ 40 * 54591 * 2
def baseEnd_54591 : Nat := 6229204979933588035877

theorem tailTrace_54591 : CollatzResearch.WordTrace tailWord_54591 prefixEnd_54591 6229204979933588035877 := by
  unfold tailWord_54591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991097345233605245635627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1327398230155736830423751 1991097345233605245635627)
  ·
    refine ⟨2986646017850407868453441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1991097345233605245635627 2986646017850407868453441)
    ·
      refine ⟨2239984513387805901340081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2986646017850407868453441 2239984513387805901340081)
      ·
        refine ⟨1679988385040854426005061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2239984513387805901340081 1679988385040854426005061)
        ·
          refine ⟨314997822195160204875949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1679988385040854426005061 314997822195160204875949)
          ·
            refine ⟨118124183323185076828481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314997822195160204875949 118124183323185076828481)
            ·
              refine ⟨88593137492388807621361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118124183323185076828481 88593137492388807621361)
              ·
                refine ⟨66444853119291605716021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88593137492388807621361 66444853119291605716021)
                ·
                  refine ⟨6229204979933588035877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66444853119291605716021 6229204979933588035877)
                  ·
                    rfl

theorem cell22_54591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].length) (baseStart_54591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54591 prefixEnd_54591 := by exact prefixLift 54591
  have htrace : WordTrace (prefixWord ++ tailWord_54591) baseStart_54591 baseEnd_54591 := by
    simpa [prefixWord, tailWord_54591, baseEnd_54591] using wordTrace_append hprefix tailTrace_54591
  have hstable : (prefixWord ++ tailWord_54591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54591).length < 2 ^ (prefixWord ++ tailWord_54591).sum := by decide
  have hdescent : baseEnd_54591 < baseStart_54591 := by decide
  rcases family_descends (prefixWord ++ tailWord_54591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54651 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 4, 3]
def baseStart_54651 : Nat := 118140960795 + 54651 * 2 ^ 59
def prefixEnd_54651 : Nat := 4983230072969 + 3 ^ 40 * 54651 * 2
def baseEnd_54651 : Nat := 18708154165980607607447

theorem tailTrace_54651 : CollatzResearch.WordTrace tailWord_54651 prefixEnd_54651 18708154165980607607447 := by
  unfold tailWord_54651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993285725016235492819807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1328857150010823661879871 1993285725016235492819807)
  ·
    refine ⟨2989928587524353239229711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993285725016235492819807 2989928587524353239229711)
    ·
      refine ⟨4484892881286529858844567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989928587524353239229711 4484892881286529858844567)
      ·
        refine ⟨6727339321929794788266851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484892881286529858844567 6727339321929794788266851)
        ·
          refine ⟨10091008982894692182400277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727339321929794788266851 10091008982894692182400277)
          ·
            refine ⟨473016046073188696050013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10091008982894692182400277 473016046073188696050013)
            ·
              refine ⟨177381017277445761018755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473016046073188696050013 177381017277445761018755)
              ·
                refine ⟨266071525916168641528133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177381017277445761018755 266071525916168641528133)
                ·
                  refine ⟨49888411109281620286525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266071525916168641528133 49888411109281620286525)
                  ·
                    refine ⟨18708154165980607607447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49888411109281620286525 18708154165980607607447)
                    ·
                      rfl

theorem cell22_54651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].length) (baseStart_54651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54651 prefixEnd_54651 := by exact prefixLift 54651
  have htrace : WordTrace (prefixWord ++ tailWord_54651) baseStart_54651 baseEnd_54651 := by
    simpa [prefixWord, tailWord_54651, baseEnd_54651] using wordTrace_append hprefix tailTrace_54651
  have hstable : (prefixWord ++ tailWord_54651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54651).length < 2 ^ (prefixWord ++ tailWord_54651).sum := by decide
  have hdescent : baseEnd_54651 < baseStart_54651 := by decide
  rcases family_descends (prefixWord ++ tailWord_54651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54679 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_54679 : Nat := 118140960795 + 54679 * 2 ^ 59
def prefixEnd_54679 : Nat := 4983230072969 + 3 ^ 40 * 54679 * 2
def baseEnd_54679 : Nat := 18717739138197867907361

theorem tailTrace_54679 : CollatzResearch.WordTrace tailWord_54679 prefixEnd_54679 18717739138197867907361 := by
  unfold tailWord_54679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994306968914796274839091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1329537979276530849892727 1994306968914796274839091)
  ·
    refine ⟨2991460453372194412258637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994306968914796274839091 2991460453372194412258637)
    ·
      refine ⟨1121797670014572904596989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991460453372194412258637 1121797670014572904596989)
      ·
        refine ⟨420674126255464839223871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1121797670014572904596989 420674126255464839223871)
        ·
          refine ⟨631011189383197258835807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420674126255464839223871 631011189383197258835807)
          ·
            refine ⟨946516784074795888253711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631011189383197258835807 946516784074795888253711)
            ·
              refine ⟨1419775176112193832380567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946516784074795888253711 1419775176112193832380567)
              ·
                refine ⟨2129662764168290748570851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419775176112193832380567 2129662764168290748570851)
                ·
                  refine ⟨3194494146252436122856277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129662764168290748570851 3194494146252436122856277)
                  ·
                    refine ⟨18717739138197867907361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3194494146252436122856277 18717739138197867907361)
                    ·
                      rfl

theorem cell22_54679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_54679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54679 prefixEnd_54679 := by exact prefixLift 54679
  have htrace : WordTrace (prefixWord ++ tailWord_54679) baseStart_54679 baseEnd_54679 := by
    simpa [prefixWord, tailWord_54679, baseEnd_54679] using wordTrace_append hprefix tailTrace_54679
  have hstable : (prefixWord ++ tailWord_54679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54679).length < 2 ^ (prefixWord ++ tailWord_54679).sum := by decide
  have hdescent : baseEnd_54679 < baseStart_54679 := by decide
  rcases family_descends (prefixWord ++ tailWord_54679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54681 : List Nat := [1, 2, 1, 2, 1, 5, 4, 6]
def baseStart_54681 : Nat := 118140960795 + 54681 * 2 ^ 59
def prefixEnd_54681 : Nat := 4983230072969 + 3 ^ 40 * 54681 * 2
def baseEnd_54681 : Nat := 2079824864341169928595

theorem tailTrace_54681 : CollatzResearch.WordTrace tailWord_54681 prefixEnd_54681 2079824864341169928595 := by
  unfold tailWord_54681
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994379914907550616411897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1329586609938367077607931 1994379914907550616411897)
  ·
    refine ⟨1495784936180662962308923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1994379914907550616411897 1495784936180662962308923)
    ·
      refine ⟨2243677404270994443463385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495784936180662962308923 2243677404270994443463385)
      ·
        refine ⟨1682758053203245832597539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243677404270994443463385 1682758053203245832597539)
        ·
          refine ⟨2524137079804868748896309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682758053203245832597539 2524137079804868748896309)
          ·
            refine ⟨236637851231706445209029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2524137079804868748896309 236637851231706445209029)
            ·
              refine ⟨44369597105944958476693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236637851231706445209029 44369597105944958476693)
              ·
                refine ⟨2079824864341169928595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44369597105944958476693 2079824864341169928595)
                ·
                  rfl

theorem cell22_54681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 6].length) (baseStart_54681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54681 prefixEnd_54681 := by exact prefixLift 54681
  have htrace : WordTrace (prefixWord ++ tailWord_54681) baseStart_54681 baseEnd_54681 := by
    simpa [prefixWord, tailWord_54681, baseEnd_54681] using wordTrace_append hprefix tailTrace_54681
  have hstable : (prefixWord ++ tailWord_54681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54681).length < 2 ^ (prefixWord ++ tailWord_54681).sum := by decide
  have hdescent : baseEnd_54681 < baseStart_54681 := by decide
  rcases family_descends (prefixWord ++ tailWord_54681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54801 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_54801 : Nat := 118140960795 + 54801 * 2 ^ 59
def prefixEnd_54801 : Nat := 4983230072969 + 3 ^ 40 * 54801 * 2
def baseEnd_54801 : Nat := 18759502231430216356987

theorem tailTrace_54801 : CollatzResearch.WordTrace tailWord_54801 prefixEnd_54801 18759502231430216356987 := by
  unfold tailWord_54801
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998756674472811110780257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1332504449648540740520171 1998756674472811110780257)
  ·
    refine ⟨1499067505854608333085193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1998756674472811110780257 1499067505854608333085193)
    ·
      refine ⟨1124300629390956249813895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1499067505854608333085193 1124300629390956249813895)
      ·
        refine ⟨1686450944086434374720843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124300629390956249813895 1686450944086434374720843)
        ·
          refine ⟨2529676416129651562081265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686450944086434374720843 2529676416129651562081265)
          ·
            refine ⟨1897257312097238671560949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2529676416129651562081265 1897257312097238671560949)
            ·
              refine ⟨177867873009116125458839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1897257312097238671560949 177867873009116125458839)
              ·
                refine ⟨266801809513674188188259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177867873009116125458839 266801809513674188188259)
                ·
                  refine ⟨400202714270511282282389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266801809513674188188259 400202714270511282282389)
                  ·
                    refine ⟨18759502231430216356987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 400202714270511282282389 18759502231430216356987)
                    ·
                      rfl

theorem cell22_54801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_54801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54801 prefixEnd_54801 := by exact prefixLift 54801
  have htrace : WordTrace (prefixWord ++ tailWord_54801) baseStart_54801 baseEnd_54801 := by
    simpa [prefixWord, tailWord_54801, baseEnd_54801] using wordTrace_append hprefix tailTrace_54801
  have hstable : (prefixWord ++ tailWord_54801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54801).length < 2 ^ (prefixWord ++ tailWord_54801).sum := by decide
  have hdescent : baseEnd_54801 < baseStart_54801 := by decide
  rcases family_descends (prefixWord ++ tailWord_54801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54805 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 4]
def baseStart_54805 : Nat := 118140960795 + 54805 * 2 ^ 59
def prefixEnd_54805 : Nat := 4983230072969 + 3 ^ 40 * 54805 * 2
def baseEnd_54805 : Nat := 6253623837725179752325

theorem tailTrace_54805 : CollatzResearch.WordTrace tailWord_54805 prefixEnd_54805 6253623837725179752325 := by
  unfold tailWord_54805
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998902566458319793925869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1332601710972213195950579 1998902566458319793925869)
  ·
    refine ⟨749588462421869922722201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1998902566458319793925869 749588462421869922722201)
    ·
      refine ⟨562191346816402442041651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 749588462421869922722201 562191346816402442041651)
      ·
        refine ⟨843287020224603663062477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562191346816402442041651 843287020224603663062477)
        ·
          refine ⟨316232632584226373648429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 843287020224603663062477 316232632584226373648429)
          ·
            refine ⟨118587237219084890118161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316232632584226373648429 118587237219084890118161)
            ·
              refine ⟨88940427914313667588621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118587237219084890118161 88940427914313667588621)
              ·
                refine ⟨33352660467867625345733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88940427914313667588621 33352660467867625345733)
                ·
                  refine ⟨6253623837725179752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33352660467867625345733 6253623837725179752325)
                  ·
                    rfl

theorem cell22_54805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_54805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54805 prefixEnd_54805 := by exact prefixLift 54805
  have htrace : WordTrace (prefixWord ++ tailWord_54805) baseStart_54805 baseEnd_54805 := by
    simpa [prefixWord, tailWord_54805, baseEnd_54805] using wordTrace_append hprefix tailTrace_54805
  have hstable : (prefixWord ++ tailWord_54805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54805).length < 2 ^ (prefixWord ++ tailWord_54805).sum := by decide
  have hdescent : baseEnd_54805 < baseStart_54805 := by decide
  rcases family_descends (prefixWord ++ tailWord_54805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54818 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_54818 : Nat := 118140960795 + 54818 * 2 ^ 59
def prefixEnd_54818 : Nat := 4983230072969 + 3 ^ 40 * 54818 * 2
def baseEnd_54818 : Nat := 18765321678847838681935

theorem tailTrace_54818 : CollatzResearch.WordTrace tailWord_54818 prefixEnd_54818 18765321678847838681935 := by
  unfold tailWord_54818
  simp only [CollatzResearch.WordTrace]
  refine ⟨499844178852805753537277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1332917810274148676099405 499844178852805753537277)
  ·
    refine ⟨187441567069802157576479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 499844178852805753537277 187441567069802157576479)
    ·
      refine ⟨281162350604703236364719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187441567069802157576479 281162350604703236364719)
      ·
        refine ⟨421743525907054854547079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281162350604703236364719 421743525907054854547079)
        ·
          refine ⟨632615288860582281820619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421743525907054854547079 632615288860582281820619)
          ·
            refine ⟨948922933290873422730929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632615288860582281820619 948922933290873422730929)
            ·
              refine ⟨711692199968155067048197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948922933290873422730929 711692199968155067048197)
              ·
                refine ⟨133442287494029075071537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711692199968155067048197 133442287494029075071537)
                ·
                  refine ⟨100081715620521806303653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133442287494029075071537 100081715620521806303653)
                  ·
                    refine ⟨18765321678847838681935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100081715620521806303653 18765321678847838681935)
                    ·
                      rfl

theorem cell22_54818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_54818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54818 prefixEnd_54818 := by exact prefixLift 54818
  have htrace : WordTrace (prefixWord ++ tailWord_54818) baseStart_54818 baseEnd_54818 := by
    simpa [prefixWord, tailWord_54818, baseEnd_54818] using wordTrace_append hprefix tailTrace_54818
  have hstable : (prefixWord ++ tailWord_54818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54818).length < 2 ^ (prefixWord ++ tailWord_54818).sum := by decide
  have hdescent : baseEnd_54818 < baseStart_54818 := by decide
  rcases family_descends (prefixWord ++ tailWord_54818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54837 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_54837 : Nat := 118140960795 + 54837 * 2 ^ 59
def prefixEnd_54837 : Nat := 4983230072969 + 3 ^ 40 * 54837 * 2
def baseEnd_54837 : Nat := 18771825767138122456877

theorem tailTrace_54837 : CollatzResearch.WordTrace tailWord_54837 prefixEnd_54837 18771825767138122456877 := by
  unfold tailWord_54837
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000069702342389259090765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1333379801561592839393843 2000069702342389259090765)
  ·
    refine ⟨750026138378395972159037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2000069702342389259090765 750026138378395972159037)
    ·
      refine ⟨281259801891898489559639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750026138378395972159037 281259801891898489559639)
      ·
        refine ⟨421889702837847734339459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281259801891898489559639 421889702837847734339459)
        ·
          refine ⟨632834554256771601509189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421889702837847734339459 632834554256771601509189)
          ·
            refine ⟨118656478923144675282973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632834554256771601509189 118656478923144675282973)
            ·
              refine ⟨44496179596179253231115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118656478923144675282973 44496179596179253231115)
              ·
                refine ⟨66744269394268879846673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44496179596179253231115 66744269394268879846673)
                ·
                  refine ⟨50058202045701659885005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66744269394268879846673 50058202045701659885005)
                  ·
                    refine ⟨18771825767138122456877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50058202045701659885005 18771825767138122456877)
                    ·
                      rfl

theorem cell22_54837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_54837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54837 prefixEnd_54837 := by exact prefixLift 54837
  have htrace : WordTrace (prefixWord ++ tailWord_54837) baseStart_54837 baseEnd_54837 := by
    simpa [prefixWord, tailWord_54837, baseEnd_54837] using wordTrace_append hprefix tailTrace_54837
  have hstable : (prefixWord ++ tailWord_54837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54837).length < 2 ^ (prefixWord ++ tailWord_54837).sum := by decide
  have hdescent : baseEnd_54837 < baseStart_54837 := by decide
  rcases family_descends (prefixWord ++ tailWord_54837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54970 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_54970 : Nat := 118140960795 + 54970 * 2 ^ 59
def prefixEnd_54970 : Nat := 4983230072969 + 3 ^ 40 * 54970 * 2
def baseEnd_54970 : Nat := 18817354385170108881469

theorem tailTrace_54970 : CollatzResearch.WordTrace tailWord_54970 prefixEnd_54970 18817354385170108881469 := by
  unfold tailWord_54970
  simp only [CollatzResearch.WordTrace]
  refine ⟨501230152715138243420591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1336613740573701982454909 501230152715138243420591)
  ·
    refine ⟨751845229072707365130887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501230152715138243420591 751845229072707365130887)
    ·
      refine ⟨1127767843609061047696331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751845229072707365130887 1127767843609061047696331)
      ·
        refine ⟨1691651765413591571544497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127767843609061047696331 1691651765413591571544497)
        ·
          refine ⟨1268738824060193678658373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691651765413591571544497 1268738824060193678658373)
          ·
            refine ⟨237888529511286314748445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1268738824060193678658373 237888529511286314748445)
            ·
              refine ⟨89208198566732368030667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237888529511286314748445 89208198566732368030667)
              ·
                refine ⟨133812297850098552046001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89208198566732368030667 133812297850098552046001)
                ·
                  refine ⟨100359223387573914034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133812297850098552046001 100359223387573914034501)
                  ·
                    refine ⟨18817354385170108881469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100359223387573914034501 18817354385170108881469)
                    ·
                      rfl

theorem cell22_54970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_54970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54970 prefixEnd_54970 := by exact prefixLift 54970
  have htrace : WordTrace (prefixWord ++ tailWord_54970) baseStart_54970 baseEnd_54970 := by
    simpa [prefixWord, tailWord_54970, baseEnd_54970] using wordTrace_append hprefix tailTrace_54970
  have hstable : (prefixWord ++ tailWord_54970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54970).length < 2 ^ (prefixWord ++ tailWord_54970).sum := by decide
  have hdescent : baseEnd_54970 < baseStart_54970 := by decide
  rcases family_descends (prefixWord ++ tailWord_54970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54989 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_54989 : Nat := 118140960795 + 54989 * 2 ^ 59
def prefixEnd_54989 : Nat := 4983230072969 + 3 ^ 40 * 54989 * 2
def baseEnd_54989 : Nat := 18823858473460392656411

theorem tailTrace_54989 : CollatzResearch.WordTrace tailWord_54989 prefixEnd_54989 18823858473460392656411 := by
  unfold tailWord_54989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005613597791719218624021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337075731861146145749347 2005613597791719218624021)
  ·
    refine ⟨94013137396486838373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2005613597791719218624021 94013137396486838373001)
    ·
      refine ⟨70509853047365128779751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94013137396486838373001 70509853047365128779751)
      ·
        refine ⟨105764779571047693169627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70509853047365128779751 105764779571047693169627)
        ·
          refine ⟨158647169356571539754441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105764779571047693169627 158647169356571539754441)
          ·
            refine ⟨118985377017428654815831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158647169356571539754441 118985377017428654815831)
            ·
              refine ⟨178478065526142982223747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118985377017428654815831 178478065526142982223747)
              ·
                refine ⟨267717098289214473335621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178478065526142982223747 267717098289214473335621)
                ·
                  refine ⟨50196955929227713750429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267717098289214473335621 50196955929227713750429)
                  ·
                    refine ⟨18823858473460392656411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50196955929227713750429 18823858473460392656411)
                    ·
                      rfl

theorem cell22_54989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_54989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_54989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_54989 prefixEnd_54989 := by exact prefixLift 54989
  have htrace : WordTrace (prefixWord ++ tailWord_54989) baseStart_54989 baseEnd_54989 := by
    simpa [prefixWord, tailWord_54989, baseEnd_54989] using wordTrace_append hprefix tailTrace_54989
  have hstable : (prefixWord ++ tailWord_54989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54989).length < 2 ^ (prefixWord ++ tailWord_54989).sum := by decide
  have hdescent : baseEnd_54989 < baseStart_54989 := by decide
  rcases family_descends (prefixWord ++ tailWord_54989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55030 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_55030 : Nat := 118140960795 + 55030 * 2 ^ 59
def prefixEnd_55030 : Nat := 4983230072969 + 3 ^ 40 * 55030 * 2
def baseEnd_55030 : Nat := 6279297870449984127095

theorem tailTrace_55030 : CollatzResearch.WordTrace tailWord_55030 prefixEnd_55030 6279297870449984127095 := by
  unfold tailWord_55030
  simp only [CollatzResearch.WordTrace]
  refine ⟨125444311915198951304159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1338072660428788813911029 125444311915198951304159)
  ·
    refine ⟨188166467872798426956239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125444311915198951304159 188166467872798426956239)
    ·
      refine ⟨282249701809197640434359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188166467872798426956239 282249701809197640434359)
      ·
        refine ⟨423374552713796460651539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282249701809197640434359 423374552713796460651539)
        ·
          refine ⟨635061829070694690977309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423374552713796460651539 635061829070694690977309)
          ·
            refine ⟨238148185901510509116491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635061829070694690977309 238148185901510509116491)
            ·
              refine ⟨357222278852265763674737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238148185901510509116491 357222278852265763674737)
              ·
                refine ⟨267916709139199322756053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357222278852265763674737 267916709139199322756053)
                ·
                  refine ⟨6279297870449984127095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267916709139199322756053 6279297870449984127095)
                  ·
                    rfl

theorem cell22_55030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_55030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55030 prefixEnd_55030 := by exact prefixLift 55030
  have htrace : WordTrace (prefixWord ++ tailWord_55030) baseStart_55030 baseEnd_55030 := by
    simpa [prefixWord, tailWord_55030, baseEnd_55030] using wordTrace_append hprefix tailTrace_55030
  have hstable : (prefixWord ++ tailWord_55030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55030).length < 2 ^ (prefixWord ++ tailWord_55030).sum := by decide
  have hdescent : baseEnd_55030 < baseStart_55030 := by decide
  rcases family_descends (prefixWord ++ tailWord_55030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55077 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_55077 : Nat := 118140960795 + 55077 * 2 ^ 59
def prefixEnd_55077 : Nat := 4983230072969 + 3 ^ 40 * 55077 * 2
def baseEnd_55077 : Nat := 18853982671857496456141

theorem tailTrace_55077 : CollatzResearch.WordTrace tailWord_55077 prefixEnd_55077 18853982671857496456141 := by
  unfold tailWord_55077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008823221472910247827485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1339215480981940165218323 2008823221472910247827485)
  ·
    refine ⟨753308708052341342935307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2008823221472910247827485 753308708052341342935307)
    ·
      refine ⟨1129963062078512014402961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753308708052341342935307 1129963062078512014402961)
      ·
        refine ⟨847472296558884010802221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1129963062078512014402961 847472296558884010802221)
        ·
          refine ⟨317802111209581504050833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847472296558884010802221 317802111209581504050833)
          ·
            refine ⟨238351583407186128038125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317802111209581504050833 238351583407186128038125)
            ·
              refine ⟨89381843777694798014297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238351583407186128038125 89381843777694798014297)
              ·
                refine ⟨67036382833271098510723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89381843777694798014297 67036382833271098510723)
                ·
                  refine ⟨100554574249906647766085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67036382833271098510723 100554574249906647766085)
                  ·
                    refine ⟨18853982671857496456141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100554574249906647766085 18853982671857496456141)
                    ·
                      rfl

theorem cell22_55077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_55077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55077 prefixEnd_55077 := by exact prefixLift 55077
  have htrace : WordTrace (prefixWord ++ tailWord_55077) baseStart_55077 baseEnd_55077 := by
    simpa [prefixWord, tailWord_55077, baseEnd_55077] using wordTrace_append hprefix tailTrace_55077
  have hstable : (prefixWord ++ tailWord_55077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55077).length < 2 ^ (prefixWord ++ tailWord_55077).sum := by decide
  have hdescent : baseEnd_55077 < baseStart_55077 := by decide
  rcases family_descends (prefixWord ++ tailWord_55077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55090 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_55090 : Nat := 118140960795 + 55090 * 2 ^ 59
def prefixEnd_55090 : Nat := 4983230072969 + 3 ^ 40 * 55090 * 2
def baseEnd_55090 : Nat := 18858432837529795881101

theorem tailTrace_55090 : CollatzResearch.WordTrace tailWord_55090 prefixEnd_55090 18858432837529795881101 := by
  unfold tailWord_55090
  simp only [CollatzResearch.WordTrace]
  refine ⟨502324342606453367012681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1339531580283875645367149 502324342606453367012681)
  ·
    refine ⟨376743256954840025259511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 502324342606453367012681 376743256954840025259511)
    ·
      refine ⟨565114885432260037889267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376743256954840025259511 565114885432260037889267)
      ·
        refine ⟨847672328148390056833901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565114885432260037889267 847672328148390056833901)
        ·
          refine ⟨317877123055646271312713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847672328148390056833901 317877123055646271312713)
          ·
            refine ⟨238407842291734703484535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317877123055646271312713 238407842291734703484535)
            ·
              refine ⟨357611763437602055226803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238407842291734703484535 357611763437602055226803)
              ·
                refine ⟨536417645156403082840205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357611763437602055226803 536417645156403082840205)
                ·
                  refine ⟨201156616933651156065077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536417645156403082840205 201156616933651156065077)
                  ·
                    refine ⟨18858432837529795881101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201156616933651156065077 18858432837529795881101)
                    ·
                      rfl

theorem cell22_55090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_55090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55090 prefixEnd_55090 := by exact prefixLift 55090
  have htrace : WordTrace (prefixWord ++ tailWord_55090) baseStart_55090 baseEnd_55090 := by
    simpa [prefixWord, tailWord_55090, baseEnd_55090] using wordTrace_append hprefix tailTrace_55090
  have hstable : (prefixWord ++ tailWord_55090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55090).length < 2 ^ (prefixWord ++ tailWord_55090).sum := by decide
  have hdescent : baseEnd_55090 < baseStart_55090 := by decide
  rcases family_descends (prefixWord ++ tailWord_55090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55103 : List Nat := [1, 1, 2, 2, 16]
def baseStart_55103 : Nat := 118140960795 + 55103 * 2 ^ 59
def prefixEnd_55103 : Nat := 4983230072969 + 3 ^ 40 * 55103 * 2
def baseEnd_55103 : Nat := 77625032934988046527

theorem tailTrace_55103 : CollatzResearch.WordTrace tailWord_55103 prefixEnd_55103 77625032934988046527 := by
  unfold tailWord_55103
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009771519378716688273963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1339847679585811125515975 2009771519378716688273963)
  ·
    refine ⟨3014657279068075032410945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009771519378716688273963 3014657279068075032410945)
    ·
      refine ⟨2260992959301056274308209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3014657279068075032410945 2260992959301056274308209)
      ·
        refine ⟨1695744719475792205731157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260992959301056274308209 1695744719475792205731157)
        ·
          refine ⟨77625032934988046527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 1695744719475792205731157 77625032934988046527)
          ·
            rfl

theorem cell22_55103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 16].length) (baseStart_55103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55103 prefixEnd_55103 := by exact prefixLift 55103
  have htrace : WordTrace (prefixWord ++ tailWord_55103) baseStart_55103 baseEnd_55103 := by
    simpa [prefixWord, tailWord_55103, baseEnd_55103] using wordTrace_append hprefix tailTrace_55103
  have hstable : (prefixWord ++ tailWord_55103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55103).length < 2 ^ (prefixWord ++ tailWord_55103).sum := by decide
  have hdescent : baseEnd_55103 < baseStart_55103 := by decide
  rcases family_descends (prefixWord ++ tailWord_55103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55107 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 2, 3]
def baseStart_55107 : Nat := 118140960795 + 55107 * 2 ^ 59
def prefixEnd_55107 : Nat := 4983230072969 + 3 ^ 40 * 55107 * 2
def baseEnd_55107 : Nat := 18864252284947418206049

theorem tailTrace_55107 : CollatzResearch.WordTrace tailWord_55107 prefixEnd_55107 18864252284947418206049 := by
  unfold tailWord_55107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009917411364225371419575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1339944940909483580946383 2009917411364225371419575)
  ·
    refine ⟨3014876117046338057129363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009917411364225371419575 3014876117046338057129363)
    ·
      refine ⟨4522314175569507085694045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014876117046338057129363 4522314175569507085694045)
      ·
        refine ⟨1695867815838565157135267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4522314175569507085694045 1695867815838565157135267)
        ·
          refine ⟨2543801723757847735702901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695867815838565157135267 2543801723757847735702901)
          ·
            refine ⟨238481411602298225222147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2543801723757847735702901 238481411602298225222147)
            ·
              refine ⟨357722117403447337833221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238481411602298225222147 357722117403447337833221)
              ·
                refine ⟨67072897013146375843729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357722117403447337833221 67072897013146375843729)
                ·
                  refine ⟨50304672759859781882797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67072897013146375843729 50304672759859781882797)
                  ·
                    refine ⟨18864252284947418206049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50304672759859781882797 18864252284947418206049)
                    ·
                      rfl

theorem cell22_55107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].length) (baseStart_55107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55107 prefixEnd_55107 := by exact prefixLift 55107
  have htrace : WordTrace (prefixWord ++ tailWord_55107) baseStart_55107 baseEnd_55107 := by
    simpa [prefixWord, tailWord_55107, baseEnd_55107] using wordTrace_append hprefix tailTrace_55107
  have hstable : (prefixWord ++ tailWord_55107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55107).length < 2 ^ (prefixWord ++ tailWord_55107).sum := by decide
  have hdescent : baseEnd_55107 < baseStart_55107 := by decide
  rcases family_descends (prefixWord ++ tailWord_55107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55124 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_55124 : Nat := 118140960795 + 55124 * 2 ^ 59
def prefixEnd_55124 : Nat := 4983230072969 + 3 ^ 40 * 55124 * 2
def baseEnd_55124 : Nat := 18870071732365040530997

theorem tailTrace_55124 : CollatzResearch.WordTrace tailWord_55124 prefixEnd_55124 18870071732365040530997 := by
  unfold tailWord_55124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005268726151318637394213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1340358301535091516525617 1005268726151318637394213)
  ·
    refine ⟨188487886153372244511415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1005268726151318637394213 188487886153372244511415)
    ·
      refine ⟨282731829230058366767123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188487886153372244511415 282731829230058366767123)
      ·
        refine ⟨424097743845087550150685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282731829230058366767123 424097743845087550150685)
        ·
          refine ⟨159036653941907831306507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424097743845087550150685 159036653941907831306507)
          ·
            refine ⟨238554980912861746959761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159036653941907831306507 238554980912861746959761)
            ·
              refine ⟨178916235684646310219821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238554980912861746959761 178916235684646310219821)
              ·
                refine ⟨67093588381742366332433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178916235684646310219821 67093588381742366332433)
                ·
                  refine ⟨50320191286306774749325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67093588381742366332433 50320191286306774749325)
                  ·
                    refine ⟨18870071732365040530997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50320191286306774749325 18870071732365040530997)
                    ·
                      rfl

theorem cell22_55124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_55124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55124 prefixEnd_55124 := by exact prefixLift 55124
  have htrace : WordTrace (prefixWord ++ tailWord_55124) baseStart_55124 baseEnd_55124 := by
    simpa [prefixWord, tailWord_55124, baseEnd_55124] using wordTrace_append hprefix tailTrace_55124
  have hstable : (prefixWord ++ tailWord_55124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55124).length < 2 ^ (prefixWord ++ tailWord_55124).sum := by decide
  have hdescent : baseEnd_55124 < baseStart_55124 := by decide
  rcases family_descends (prefixWord ++ tailWord_55124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55139 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 2, 4]
def baseStart_55139 : Nat := 118140960795 + 55139 * 2 ^ 59
def prefixEnd_55139 : Nat := 4983230072969 + 3 ^ 40 * 55139 * 2
def baseEnd_55139 : Nat := 18875206538910001405951

theorem tailTrace_55139 : CollatzResearch.WordTrace tailWord_55139 prefixEnd_55139 18875206538910001405951 := by
  unfold tailWord_55139
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011084547248294836584471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1340723031498863224389647 2011084547248294836584471)
  ·
    refine ⟨3016626820872442254876707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011084547248294836584471 3016626820872442254876707)
    ·
      refine ⟨4524940231308663382315061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016626820872442254876707 4524940231308663382315061)
      ·
        refine ⟨424213146685187192092037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4524940231308663382315061 424213146685187192092037)
        ·
          refine ⟨79539965003472598517257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424213146685187192092037 79539965003472598517257)
          ·
            refine ⟨59654973752604448887943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79539965003472598517257 59654973752604448887943)
            ·
              refine ⟨89482460628906673331915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59654973752604448887943 89482460628906673331915)
              ·
                refine ⟨134223690943360009997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89482460628906673331915 134223690943360009997873)
                ·
                  refine ⟨100667768207520007498405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134223690943360009997873 100667768207520007498405)
                  ·
                    refine ⟨18875206538910001405951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100667768207520007498405 18875206538910001405951)
                    ·
                      rfl

theorem cell22_55139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].length) (baseStart_55139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55139 prefixEnd_55139 := by exact prefixLift 55139
  have htrace : WordTrace (prefixWord ++ tailWord_55139) baseStart_55139 baseEnd_55139 := by
    simpa [prefixWord, tailWord_55139, baseEnd_55139] using wordTrace_append hprefix tailTrace_55139
  have hstable : (prefixWord ++ tailWord_55139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55139).length < 2 ^ (prefixWord ++ tailWord_55139).sum := by decide
  have hdescent : baseEnd_55139 < baseStart_55139 := by decide
  rcases family_descends (prefixWord ++ tailWord_55139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55158 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_55158 : Nat := 118140960795 + 55158 * 2 ^ 59
def prefixEnd_55158 : Nat := 4983230072969 + 3 ^ 40 * 55158 * 2
def baseEnd_55158 : Nat := 18881710627200285180893

theorem tailTrace_55158 : CollatzResearch.WordTrace tailWord_55158 prefixEnd_55158 18881710627200285180893 := by
  unfold tailWord_55158
  simp only [CollatzResearch.WordTrace]
  refine ⟨125736095886216317595383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1341185022786307387684085 125736095886216317595383)
  ·
    refine ⟨188604143829324476393075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125736095886216317595383 188604143829324476393075)
    ·
      refine ⟨282906215743986714589613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188604143829324476393075 282906215743986714589613)
      ·
        refine ⟨106089830903995017971105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282906215743986714589613 106089830903995017971105)
        ·
          refine ⟨79567373177996263478329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106089830903995017971105 79567373177996263478329)
          ·
            refine ⟨59675529883497197608747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79567373177996263478329 59675529883497197608747)
            ·
              refine ⟨89513294825245796413121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59675529883497197608747 89513294825245796413121)
              ·
                refine ⟨67134971118934347309841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89513294825245796413121 67134971118934347309841)
                ·
                  refine ⟨50351228339200760482381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67134971118934347309841 50351228339200760482381)
                  ·
                    refine ⟨18881710627200285180893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50351228339200760482381 18881710627200285180893)
                    ·
                      rfl

theorem cell22_55158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_55158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55158 prefixEnd_55158 := by exact prefixLift 55158
  have htrace : WordTrace (prefixWord ++ tailWord_55158) baseStart_55158 baseEnd_55158 := by
    simpa [prefixWord, tailWord_55158, baseEnd_55158] using wordTrace_append hprefix tailTrace_55158
  have hstable : (prefixWord ++ tailWord_55158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55158).length < 2 ^ (prefixWord ++ tailWord_55158).sum := by decide
  have hdescent : baseEnd_55158 < baseStart_55158 := by decide
  rcases family_descends (prefixWord ++ tailWord_55158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55220 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_55220 : Nat := 118140960795 + 55220 * 2 ^ 59
def prefixEnd_55220 : Nat := 4983230072969 + 3 ^ 40 * 55220 * 2
def baseEnd_55220 : Nat := 18902934494252790130703

theorem tailTrace_55220 : CollatzResearch.WordTrace tailWord_55220 prefixEnd_55220 18902934494252790130703 := by
  unfold tailWord_55220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007019429977422835141557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1342692573303230446855409 1007019429977422835141557)
  ·
    refine ⟨94408071560383390794521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1007019429977422835141557 94408071560383390794521)
    ·
      refine ⟨70806053670287543095891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94408071560383390794521 70806053670287543095891)
      ·
        refine ⟨106209080505431314643837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70806053670287543095891 106209080505431314643837)
        ·
          refine ⟨39828405189536742991439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106209080505431314643837 39828405189536742991439)
          ·
            refine ⟨59742607784305114487159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39828405189536742991439 59742607784305114487159)
            ·
              refine ⟨89613911676457671730739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59742607784305114487159 89613911676457671730739)
              ·
                refine ⟨134420867514686507596109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89613911676457671730739 134420867514686507596109)
                ·
                  refine ⟨50407825318007440348541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134420867514686507596109 50407825318007440348541)
                  ·
                    refine ⟨18902934494252790130703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50407825318007440348541 18902934494252790130703)
                    ·
                      rfl

theorem cell22_55220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_55220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55220 prefixEnd_55220 := by exact prefixLift 55220
  have htrace : WordTrace (prefixWord ++ tailWord_55220) baseStart_55220 baseEnd_55220 := by
    simpa [prefixWord, tailWord_55220, baseEnd_55220] using wordTrace_append hprefix tailTrace_55220
  have hstable : (prefixWord ++ tailWord_55220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55220).length < 2 ^ (prefixWord ++ tailWord_55220).sum := by decide
  have hdescent : baseEnd_55220 < baseStart_55220 := by decide
  rcases family_descends (prefixWord ++ tailWord_55220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55255 : List Nat := [1, 1, 3, 2, 1, 1, 3, 10]
def baseStart_55255 : Nat := 118140960795 + 55255 * 2 ^ 59
def prefixEnd_55255 : Nat := 4983230072969 + 3 ^ 40 * 55255 * 2
def baseEnd_55255 : Nat := 2101657301058262833955

theorem tailTrace_55255 : CollatzResearch.WordTrace tailWord_55255 prefixEnd_55255 2101657301058262833955 := by
  unfold tailWord_55255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015315414828046647807219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1343543609885364431871479 2015315414828046647807219)
  ·
    refine ⟨3022973122242069971710829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015315414828046647807219 3022973122242069971710829)
    ·
      refine ⟨1133614920840776239391561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3022973122242069971710829 1133614920840776239391561)
      ·
        refine ⟨850211190630582179543671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133614920840776239391561 850211190630582179543671)
        ·
          refine ⟨1275316785945873269315507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850211190630582179543671 1275316785945873269315507)
          ·
            refine ⟨1912975178918809903973261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275316785945873269315507 1912975178918809903973261)
            ·
              refine ⟨717365692094553713989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1912975178918809903973261 717365692094553713989973)
              ·
                refine ⟨2101657301058262833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 717365692094553713989973 2101657301058262833955)
                ·
                  rfl

theorem cell22_55255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 10].length) (baseStart_55255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55255 prefixEnd_55255 := by exact prefixLift 55255
  have htrace : WordTrace (prefixWord ++ tailWord_55255) baseStart_55255 baseEnd_55255 := by
    simpa [prefixWord, tailWord_55255, baseEnd_55255] using wordTrace_append hprefix tailTrace_55255
  have hstable : (prefixWord ++ tailWord_55255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55255).length < 2 ^ (prefixWord ++ tailWord_55255).sum := by decide
  have hdescent : baseEnd_55255 < baseStart_55255 := by decide
  rcases family_descends (prefixWord ++ tailWord_55255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55278 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_55278 : Nat := 118140960795 + 55278 * 2 ^ 59
def prefixEnd_55278 : Nat := 4983230072969 + 3 ^ 40 * 55278 * 2
def baseEnd_55278 : Nat := 6307596359853324060175

theorem tailTrace_55278 : CollatzResearch.WordTrace tailWord_55278 prefixEnd_55278 6307596359853324060175 := by
  unfold tailWord_55278
  simp only [CollatzResearch.WordTrace]
  refine ⟨252019286718090196986811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1344102862496481050596325 252019286718090196986811)
  ·
    refine ⟨378028930077135295480217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252019286718090196986811 378028930077135295480217)
    ·
      refine ⟨283521697557851471610163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378028930077135295480217 283521697557851471610163)
      ·
        refine ⟨425282546336777207415245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283521697557851471610163 425282546336777207415245)
        ·
          refine ⟨159480954876291452780717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425282546336777207415245 159480954876291452780717)
          ·
            refine ⟨59805358078609294792769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159480954876291452780717 59805358078609294792769)
            ·
              refine ⟨44854018558956971094577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59805358078609294792769 44854018558956971094577)
              ·
                refine ⟨33640513919217728320933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44854018558956971094577 33640513919217728320933)
                ·
                  refine ⟨6307596359853324060175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33640513919217728320933 6307596359853324060175)
                  ·
                    rfl

theorem cell22_55278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_55278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55278 prefixEnd_55278 := by exact prefixLift 55278
  have htrace : WordTrace (prefixWord ++ tailWord_55278) baseStart_55278 baseEnd_55278 := by
    simpa [prefixWord, tailWord_55278, baseEnd_55278] using wordTrace_append hprefix tailTrace_55278
  have hstable : (prefixWord ++ tailWord_55278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55278).length < 2 ^ (prefixWord ++ tailWord_55278).sum := by decide
  have hdescent : baseEnd_55278 < baseStart_55278 := by decide
  rcases family_descends (prefixWord ++ tailWord_55278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55287 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 9, 3]
def baseStart_55287 : Nat := 118140960795 + 55287 * 2 ^ 59
def prefixEnd_55287 : Nat := 4983230072969 + 3 ^ 40 * 55287 * 2
def baseEnd_55287 : Nat := 18925869963486948705497

theorem tailTrace_55287 : CollatzResearch.WordTrace tailWord_55287 prefixEnd_55287 18925869963486948705497 := by
  unfold tailWord_55287
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016482550712116112972115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1344321700474744075314743 2016482550712116112972115)
  ·
    refine ⟨3024723826068174169458173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2016482550712116112972115 3024723826068174169458173)
    ·
      refine ⟨1134271434775565313546815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3024723826068174169458173 1134271434775565313546815)
      ·
        refine ⟨1701407152163347970320223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134271434775565313546815 1701407152163347970320223)
        ·
          refine ⟨2552110728245021955480335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701407152163347970320223 2552110728245021955480335)
          ·
            refine ⟨3828166092367532933220503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552110728245021955480335 3828166092367532933220503)
            ·
              refine ⟨5742249138551299399830755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828166092367532933220503 5742249138551299399830755)
              ·
                refine ⟨8613373707826949099746133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742249138551299399830755 8613373707826949099746133)
                ·
                  refine ⟨50468986569298529881325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8613373707826949099746133 50468986569298529881325)
                  ·
                    refine ⟨18925869963486948705497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50468986569298529881325 18925869963486948705497)
                    ·
                      rfl

theorem cell22_55287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_55287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55287 prefixEnd_55287 := by exact prefixLift 55287
  have htrace : WordTrace (prefixWord ++ tailWord_55287) baseStart_55287 baseEnd_55287 := by
    simpa [prefixWord, tailWord_55287, baseEnd_55287] using wordTrace_append hprefix tailTrace_55287
  have hstable : (prefixWord ++ tailWord_55287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55287).length < 2 ^ (prefixWord ++ tailWord_55287).sum := by decide
  have hdescent : baseEnd_55287 < baseStart_55287 := by decide
  rcases family_descends (prefixWord ++ tailWord_55287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55304 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_55304 : Nat := 118140960795 + 55304 * 2 ^ 59
def prefixEnd_55304 : Nat := 4983230072969 + 3 ^ 40 * 55304 * 2
def baseEnd_55304 : Nat := 18931689410904571030445

theorem tailTrace_55304 : CollatzResearch.WordTrace tailWord_55304 prefixEnd_55304 18931689410904571030445 := by
  unfold tailWord_55304
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008551295825264008170483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1344735061100352010893977 1008551295825264008170483)
  ·
    refine ⟨1512826943737896012255725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008551295825264008170483 1512826943737896012255725)
    ·
      refine ⟨567310103901711004595897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1512826943737896012255725 567310103901711004595897)
      ·
        refine ⟨425482577926283253446923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567310103901711004595897 425482577926283253446923)
        ·
          refine ⟨638223866889424880170385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425482577926283253446923 638223866889424880170385)
          ·
            refine ⟨478667900167068660127789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638223866889424880170385 478667900167068660127789)
            ·
              refine ⟨179500462562650747547921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478667900167068660127789 179500462562650747547921)
              ·
                refine ⟨134625346921988060660941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179500462562650747547921 134625346921988060660941)
                ·
                  refine ⟨50484505095745522747853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134625346921988060660941 50484505095745522747853)
                  ·
                    refine ⟨18931689410904571030445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50484505095745522747853 18931689410904571030445)
                    ·
                      rfl

theorem cell22_55304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_55304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55304 prefixEnd_55304 := by exact prefixLift 55304
  have htrace : WordTrace (prefixWord ++ tailWord_55304) baseStart_55304 baseEnd_55304 := by
    simpa [prefixWord, tailWord_55304, baseEnd_55304] using wordTrace_append hprefix tailTrace_55304
  have hstable : (prefixWord ++ tailWord_55304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55304).length < 2 ^ (prefixWord ++ tailWord_55304).sum := by decide
  have hdescent : baseEnd_55304 < baseStart_55304 := by decide
  rcases family_descends (prefixWord ++ tailWord_55304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55338 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_55338 : Nat := 118140960795 + 55338 * 2 ^ 59
def prefixEnd_55338 : Nat := 4983230072969 + 3 ^ 40 * 55338 * 2
def baseEnd_55338 : Nat := 18943328305739815680341

theorem tailTrace_55338 : CollatzResearch.WordTrace tailWord_55338 prefixEnd_55338 18943328305739815680341 := by
  unfold tailWord_55338
  simp only [CollatzResearch.WordTrace]
  refine ⟨504585668381837955769667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1345561782351567882052445 504585668381837955769667)
  ·
    refine ⟨756878502572756933654501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 504585668381837955769667 756878502572756933654501)
    ·
      refine ⟨141914719232391925060219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 756878502572756933654501 141914719232391925060219)
      ·
        refine ⟨212872078848587887590329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141914719232391925060219 212872078848587887590329)
        ·
          refine ⟨159654059136440915692747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212872078848587887590329 159654059136440915692747)
          ·
            refine ⟨239481088704661373539121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159654059136440915692747 239481088704661373539121)
            ·
              refine ⟨179610816528496030154341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239481088704661373539121 179610816528496030154341)
              ·
                refine ⟨33677028099093005653939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179610816528496030154341 33677028099093005653939)
                ·
                  refine ⟨50515542148639508480909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33677028099093005653939 50515542148639508480909)
                  ·
                    refine ⟨18943328305739815680341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50515542148639508480909 18943328305739815680341)
                    ·
                      rfl

theorem cell22_55338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_55338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55338 prefixEnd_55338 := by exact prefixLift 55338
  have htrace : WordTrace (prefixWord ++ tailWord_55338) baseStart_55338 baseEnd_55338 := by
    simpa [prefixWord, tailWord_55338, baseEnd_55338] using wordTrace_append hprefix tailTrace_55338
  have hstable : (prefixWord ++ tailWord_55338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55338).length < 2 ^ (prefixWord ++ tailWord_55338).sum := by decide
  have hdescent : baseEnd_55338 < baseStart_55338 := by decide
  rcases family_descends (prefixWord ++ tailWord_55338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55347 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_55347 : Nat := 118140960795 + 55347 * 2 ^ 59
def prefixEnd_55347 : Nat := 4983230072969 + 3 ^ 40 * 55347 * 2
def baseEnd_55347 : Nat := 18946409189666792205313

theorem tailTrace_55347 : CollatzResearch.WordTrace tailWord_55347 prefixEnd_55347 18946409189666792205313 := by
  unfold tailWord_55347
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018670930494746360156295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1345780620329830906770863 2018670930494746360156295)
  ·
    refine ⟨3028006395742119540234443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018670930494746360156295 3028006395742119540234443)
    ·
      refine ⟨4542009593613179310351665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028006395742119540234443 4542009593613179310351665)
      ·
        refine ⟨3406507195209884482763749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4542009593613179310351665 3406507195209884482763749)
        ·
          refine ⟨638720099101853340518203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3406507195209884482763749 638720099101853340518203)
          ·
            refine ⟨958080148652780010777305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638720099101853340518203 958080148652780010777305)
            ·
              refine ⟨718560111489585008082979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958080148652780010777305 718560111489585008082979)
              ·
                refine ⟨1077840167234377512124469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718560111489585008082979 1077840167234377512124469)
                ·
                  refine ⟨101047515678222891761669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1077840167234377512124469 101047515678222891761669)
                  ·
                    refine ⟨18946409189666792205313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101047515678222891761669 18946409189666792205313)
                    ·
                      rfl

theorem cell22_55347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_55347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55347 prefixEnd_55347 := by exact prefixLift 55347
  have htrace : WordTrace (prefixWord ++ tailWord_55347) baseStart_55347 baseEnd_55347 := by
    simpa [prefixWord, tailWord_55347, baseEnd_55347] using wordTrace_append hprefix tailTrace_55347
  have hstable : (prefixWord ++ tailWord_55347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55347).length < 2 ^ (prefixWord ++ tailWord_55347).sum := by decide
  have hdescent : baseEnd_55347 < baseStart_55347 := by decide
  rcases family_descends (prefixWord ++ tailWord_55347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55377 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_55377 : Nat := 118140960795 + 55377 * 2 ^ 59
def prefixEnd_55377 : Nat := 4983230072969 + 3 ^ 40 * 55377 * 2
def baseEnd_55377 : Nat := 18956678802756713955221

theorem tailTrace_55377 : CollatzResearch.WordTrace tailWord_55377 prefixEnd_55377 18956678802756713955221 := by
  unfold tailWord_55377
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019765120386061483748385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1346510080257374322498923 2019765120386061483748385)
  ·
    refine ⟨1514823840289546112811289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2019765120386061483748385 1514823840289546112811289)
    ·
      refine ⟨1136117880217159584608467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514823840289546112811289 1136117880217159584608467)
      ·
        refine ⟨1704176820325739376912701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136117880217159584608467 1704176820325739376912701)
        ·
          refine ⟨639066307622152266342263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1704176820325739376912701 639066307622152266342263)
          ·
            refine ⟨958599461433228399513395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639066307622152266342263 958599461433228399513395)
            ·
              refine ⟨1437899192149842599270093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958599461433228399513395 1437899192149842599270093)
              ·
                refine ⟨539212197056190974726285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437899192149842599270093 539212197056190974726285)
                ·
                  refine ⟨202204573896071615522357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539212197056190974726285 202204573896071615522357)
                  ·
                    refine ⟨18956678802756713955221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202204573896071615522357 18956678802756713955221)
                    ·
                      rfl

theorem cell22_55377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_55377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55377 prefixEnd_55377 := by exact prefixLift 55377
  have htrace : WordTrace (prefixWord ++ tailWord_55377) baseStart_55377 baseEnd_55377 := by
    simpa [prefixWord, tailWord_55377, baseEnd_55377] using wordTrace_append hprefix tailTrace_55377
  have hstable : (prefixWord ++ tailWord_55377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55377).length < 2 ^ (prefixWord ++ tailWord_55377).sum := by decide
  have hdescent : baseEnd_55377 < baseStart_55377 := by decide
  rcases family_descends (prefixWord ++ tailWord_55377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55407 : List Nat := [1, 1, 2, 1, 3, 4, 1, 9]
def baseStart_55407 : Nat := 118140960795 + 55407 * 2 ^ 59
def prefixEnd_55407 : Nat := 4983230072969 + 3 ^ 40 * 55407 * 2
def baseEnd_55407 : Nat := 2107438712871848411681

theorem tailTrace_55407 : CollatzResearch.WordTrace tailWord_55407 prefixEnd_55407 2107438712871848411681 := by
  unfold tailWord_55407
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020859310277376607340475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1347239540184917738226983 2020859310277376607340475)
  ·
    refine ⟨3031288965416064911010713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2020859310277376607340475 3031288965416064911010713)
    ·
      refine ⟨2273466724062048683258035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3031288965416064911010713 2273466724062048683258035)
      ·
        refine ⟨3410200086093073024887053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273466724062048683258035 3410200086093073024887053)
        ·
          refine ⟨1278825032284902384332645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3410200086093073024887053 1278825032284902384332645)
          ·
            refine ⟨239779693553419197062371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1278825032284902384332645 239779693553419197062371)
            ·
              refine ⟨359669540330128795593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239779693553419197062371 359669540330128795593557)
              ·
                refine ⟨2107438712871848411681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 359669540330128795593557 2107438712871848411681)
                ·
                  rfl

theorem cell22_55407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 9].length) (baseStart_55407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55407 prefixEnd_55407 := by exact prefixLift 55407
  have htrace : WordTrace (prefixWord ++ tailWord_55407) baseStart_55407 baseEnd_55407 := by
    simpa [prefixWord, tailWord_55407, baseEnd_55407] using wordTrace_append hprefix tailTrace_55407
  have hstable : (prefixWord ++ tailWord_55407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55407).length < 2 ^ (prefixWord ++ tailWord_55407).sum := by decide
  have hdescent : baseEnd_55407 < baseStart_55407 := by decide
  rcases family_descends (prefixWord ++ tailWord_55407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55473 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_55473 : Nat := 118140960795 + 55473 * 2 ^ 59
def prefixEnd_55473 : Nat := 4983230072969 + 3 ^ 40 * 55473 * 2
def baseEnd_55473 : Nat := 18989541564644463554927

theorem tailTrace_55473 : CollatzResearch.WordTrace tailWord_55473 prefixEnd_55473 18989541564644463554927 := by
  unfold tailWord_55473
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023266528038269879243073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1348844352025513252828715 2023266528038269879243073)
  ·
    refine ⟨1517449896028702409432305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023266528038269879243073 1517449896028702409432305)
    ·
      refine ⟨1138087422021526807074229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517449896028702409432305 1138087422021526807074229)
      ·
        refine ⟨106695695814518138163209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1138087422021526807074229 106695695814518138163209)
        ·
          refine ⟨80021771860888603622407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106695695814518138163209 80021771860888603622407)
          ·
            refine ⟨120032657791332905433611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80021771860888603622407 120032657791332905433611)
            ·
              refine ⟨180048986686999358150417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120032657791332905433611 180048986686999358150417)
              ·
                refine ⟨135036740015249518612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180048986686999358150417 135036740015249518612813)
                ·
                  refine ⟨50638777505718569479805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135036740015249518612813 50638777505718569479805)
                  ·
                    refine ⟨18989541564644463554927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50638777505718569479805 18989541564644463554927)
                    ·
                      rfl

theorem cell22_55473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_55473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55473 prefixEnd_55473 := by exact prefixLift 55473
  have htrace : WordTrace (prefixWord ++ tailWord_55473) baseStart_55473 baseEnd_55473 := by
    simpa [prefixWord, tailWord_55473, baseEnd_55473] using wordTrace_append hprefix tailTrace_55473
  have hstable : (prefixWord ++ tailWord_55473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55473).length < 2 ^ (prefixWord ++ tailWord_55473).sum := by decide
  have hdescent : baseEnd_55473 < baseStart_55473 := by decide
  rcases family_descends (prefixWord ++ tailWord_55473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55514 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_55514 : Nat := 118140960795 + 55514 * 2 ^ 59
def prefixEnd_55514 : Nat := 4983230072969 + 3 ^ 40 * 55514 * 2
def baseEnd_55514 : Nat := 6334525567511341093267

theorem tailTrace_55514 : CollatzResearch.WordTrace tailWord_55514 prefixEnd_55514 6334525567511341093267 := by
  unfold tailWord_55514
  simp only [CollatzResearch.WordTrace]
  refine ⟨506190480222433470371399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1349841280593155920990397 506190480222433470371399)
  ·
    refine ⟨759285720333650205557099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506190480222433470371399 759285720333650205557099)
    ·
      refine ⟨1138928580500475308335649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759285720333650205557099 1138928580500475308335649)
      ·
        refine ⟨854196435375356481251737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138928580500475308335649 854196435375356481251737)
        ·
          refine ⟨640647326531517360938803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854196435375356481251737 640647326531517360938803)
          ·
            refine ⟨960970989797276041408205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640647326531517360938803 960970989797276041408205)
            ·
              refine ⟨360364121173978515528077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960970989797276041408205 360364121173978515528077)
              ·
                refine ⟨135136545440241943323029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360364121173978515528077 135136545440241943323029)
                ·
                  refine ⟨6334525567511341093267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135136545440241943323029 6334525567511341093267)
                  ·
                    rfl

theorem cell22_55514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_55514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55514 prefixEnd_55514 := by exact prefixLift 55514
  have htrace : WordTrace (prefixWord ++ tailWord_55514) baseStart_55514 baseEnd_55514 := by
    simpa [prefixWord, tailWord_55514, baseEnd_55514] using wordTrace_append hprefix tailTrace_55514
  have hstable : (prefixWord ++ tailWord_55514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55514).length < 2 ^ (prefixWord ++ tailWord_55514).sum := by decide
  have hdescent : baseEnd_55514 < baseStart_55514 := by decide
  rcases family_descends (prefixWord ++ tailWord_55514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55544 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_55544 : Nat := 118140960795 + 55544 * 2 ^ 59
def prefixEnd_55544 : Nat := 4983230072969 + 3 ^ 40 * 55544 * 2
def baseEnd_55544 : Nat := 19013846315623945029709

theorem tailTrace_55544 : CollatzResearch.WordTrace tailWord_55544 prefixEnd_55544 19013846315623945029709 := by
  unfold tailWord_55544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012928055390524502538843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1350570740520699336718457 1012928055390524502538843)
  ·
    refine ⟨1519392083085786753808265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012928055390524502538843 1519392083085786753808265)
    ·
      refine ⟨1139544062314340065356199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1519392083085786753808265 1139544062314340065356199)
      ·
        refine ⟨1709316093471510098034299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139544062314340065356199 1709316093471510098034299)
        ·
          refine ⟨2563974140207265147051449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709316093471510098034299 2563974140207265147051449)
          ·
            refine ⟨1922980605155448860288587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2563974140207265147051449 1922980605155448860288587)
            ·
              refine ⟨2884470907733173290432881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922980605155448860288587 2884470907733173290432881)
              ·
                refine ⟨2163353180799879967824661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884470907733173290432881 2163353180799879967824661)
                ·
                  refine ⟨101407180349994373491781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2163353180799879967824661 101407180349994373491781)
                  ·
                    refine ⟨19013846315623945029709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101407180349994373491781 19013846315623945029709)
                    ·
                      rfl

theorem cell22_55544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_55544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55544 prefixEnd_55544 := by exact prefixLift 55544
  have htrace : WordTrace (prefixWord ++ tailWord_55544) baseStart_55544 baseEnd_55544 := by
    simpa [prefixWord, tailWord_55544, baseEnd_55544] using wordTrace_append hprefix tailTrace_55544
  have hstable : (prefixWord ++ tailWord_55544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55544).length < 2 ^ (prefixWord ++ tailWord_55544).sum := by decide
  have hdescent : baseEnd_55544 < baseStart_55544 := by decide
  rcases family_descends (prefixWord ++ tailWord_55544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55546 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_55546 : Nat := 118140960795 + 55546 * 2 ^ 59
def prefixEnd_55546 : Nat := 4983230072969 + 3 ^ 40 * 55546 * 2
def baseEnd_55546 : Nat := 19014530956496606479703

theorem tailTrace_55546 : CollatzResearch.WordTrace tailWord_55546 prefixEnd_55546 19014530956496606479703 := by
  unfold tailWord_55546
  simp only [CollatzResearch.WordTrace]
  refine ⟨506482264193450836662623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1350619371182535564433661 506482264193450836662623)
  ·
    refine ⟨759723396290176254993935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506482264193450836662623 759723396290176254993935)
    ·
      refine ⟨1139585094435264382490903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759723396290176254993935 1139585094435264382490903)
      ·
        refine ⟨1709377641652896573736355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139585094435264382490903 1709377641652896573736355)
        ·
          refine ⟨2564066462479344860604533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709377641652896573736355 2564066462479344860604533)
          ·
            refine ⟨240381230857438580681675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2564066462479344860604533 240381230857438580681675)
            ·
              refine ⟨360571846286157871022513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240381230857438580681675 360571846286157871022513)
              ·
                refine ⟨270428884714618403266885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360571846286157871022513 270428884714618403266885)
                ·
                  refine ⟨50705415883990950612541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270428884714618403266885 50705415883990950612541)
                  ·
                    refine ⟨19014530956496606479703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50705415883990950612541 19014530956496606479703)
                    ·
                      rfl

theorem cell22_55546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_55546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55546 prefixEnd_55546 := by exact prefixLift 55546
  have htrace : WordTrace (prefixWord ++ tailWord_55546) baseStart_55546 baseEnd_55546 := by
    simpa [prefixWord, tailWord_55546, baseEnd_55546] using wordTrace_append hprefix tailTrace_55546
  have hstable : (prefixWord ++ tailWord_55546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55546).length < 2 ^ (prefixWord ++ tailWord_55546).sum := by decide
  have hdescent : baseEnd_55546 < baseStart_55546 := by decide
  rcases family_descends (prefixWord ++ tailWord_55546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55548 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_55548 : Nat := 118140960795 + 55548 * 2 ^ 59
def prefixEnd_55548 : Nat := 4983230072969 + 3 ^ 40 * 55548 * 2
def baseEnd_55548 : Nat := 6338405199123089309899

theorem tailTrace_55548 : CollatzResearch.WordTrace tailWord_55548 prefixEnd_55548 6338405199123089309899 := by
  unfold tailWord_55548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013001001383278844111649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1350668001844371792148865 1013001001383278844111649)
  ·
    refine ⟨759750751037459133083737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013001001383278844111649 759750751037459133083737)
    ·
      refine ⟨569813063278094349812803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759750751037459133083737 569813063278094349812803)
      ·
        refine ⟨854719594917141524719205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569813063278094349812803 854719594917141524719205)
        ·
          refine ⟨160259924046964035884851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 854719594917141524719205 160259924046964035884851)
          ·
            refine ⟨240389886070446053827277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160259924046964035884851 240389886070446053827277)
            ·
              refine ⟨90146207276417270185229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240389886070446053827277 90146207276417270185229)
              ·
                refine ⟨33804827728656476319461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90146207276417270185229 33804827728656476319461)
                ·
                  refine ⟨6338405199123089309899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33804827728656476319461 6338405199123089309899)
                  ·
                    rfl

theorem cell22_55548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_55548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55548 prefixEnd_55548 := by exact prefixLift 55548
  have htrace : WordTrace (prefixWord ++ tailWord_55548) baseStart_55548 baseEnd_55548 := by
    simpa [prefixWord, tailWord_55548, baseEnd_55548] using wordTrace_append hprefix tailTrace_55548
  have hstable : (prefixWord ++ tailWord_55548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55548).length < 2 ^ (prefixWord ++ tailWord_55548).sum := by decide
  have hdescent : baseEnd_55548 < baseStart_55548 := by decide
  rcases family_descends (prefixWord ++ tailWord_55548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55561 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_55561 : Nat := 118140960795 + 55561 * 2 ^ 59
def prefixEnd_55561 : Nat := 4983230072969 + 3 ^ 40 * 55561 * 2
def baseEnd_55561 : Nat := 19019665763041567354657

theorem tailTrace_55561 : CollatzResearch.WordTrace tailWord_55561 prefixEnd_55561 19019665763041567354657 := by
  unfold tailWord_55561
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026476151719460908446537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1350984101146307272297691 2026476151719460908446537)
  ·
    refine ⟨1519857113789595681334903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2026476151719460908446537 1519857113789595681334903)
    ·
      refine ⟨2279785670684393522002355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519857113789595681334903 2279785670684393522002355)
      ·
        refine ⟨3419678506026590283003533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279785670684393522002355 3419678506026590283003533)
        ·
          refine ⟨1282379439759971356126325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3419678506026590283003533 1282379439759971356126325)
          ·
            refine ⟨120223072477497314636843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1282379439759971356126325 120223072477497314636843)
            ·
              refine ⟨180334608716245971955265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120223072477497314636843 180334608716245971955265)
              ·
                refine ⟨135250956537184478966449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180334608716245971955265 135250956537184478966449)
                ·
                  refine ⟨101438217402888359224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135250956537184478966449 101438217402888359224837)
                  ·
                    refine ⟨19019665763041567354657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101438217402888359224837 19019665763041567354657)
                    ·
                      rfl

theorem cell22_55561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_55561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55561 prefixEnd_55561 := by exact prefixLift 55561
  have htrace : WordTrace (prefixWord ++ tailWord_55561) baseStart_55561 baseEnd_55561 := by
    simpa [prefixWord, tailWord_55561, baseEnd_55561] using wordTrace_append hprefix tailTrace_55561
  have hstable : (prefixWord ++ tailWord_55561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55561).length < 2 ^ (prefixWord ++ tailWord_55561).sum := by decide
  have hdescent : baseEnd_55561 < baseStart_55561 := by decide
  rcases family_descends (prefixWord ++ tailWord_55561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55636 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_55636 : Nat := 118140960795 + 55636 * 2 ^ 59
def prefixEnd_55636 : Nat := 4983230072969 + 3 ^ 40 * 55636 * 2
def baseEnd_55636 : Nat := 19045339795766371729427

theorem tailTrace_55636 : CollatzResearch.WordTrace tailWord_55636 prefixEnd_55636 19045339795766371729427 := by
  unfold tailWord_55636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014605813223874358713381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1352807750965165811617841 1014605813223874358713381)
  ·
    refine ⟨190238589979476442258759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1014605813223874358713381 190238589979476442258759)
    ·
      refine ⟨285357884969214663388139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190238589979476442258759 285357884969214663388139)
      ·
        refine ⟨428036827453821995082209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285357884969214663388139 428036827453821995082209)
        ·
          refine ⟨321027620590366496311657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428036827453821995082209 321027620590366496311657)
          ·
            refine ⟨240770715442774872233743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321027620590366496311657 240770715442774872233743)
            ·
              refine ⟨361156073164162308350615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240770715442774872233743 361156073164162308350615)
              ·
                refine ⟨541734109746243462525923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361156073164162308350615 541734109746243462525923)
                ·
                  refine ⟨812601164619365193788885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541734109746243462525923 812601164619365193788885)
                  ·
                    refine ⟨19045339795766371729427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 812601164619365193788885 19045339795766371729427)
                    ·
                      rfl

theorem cell22_55636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_55636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55636 prefixEnd_55636 := by exact prefixLift 55636
  have htrace : WordTrace (prefixWord ++ tailWord_55636) baseStart_55636 baseEnd_55636 := by
    simpa [prefixWord, tailWord_55636, baseEnd_55636] using wordTrace_append hprefix tailTrace_55636
  have hstable : (prefixWord ++ tailWord_55636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55636).length < 2 ^ (prefixWord ++ tailWord_55636).sum := by decide
  have hdescent : baseEnd_55636 < baseStart_55636 := by decide
  rcases family_descends (prefixWord ++ tailWord_55636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55646 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_55646 : Nat := 118140960795 + 55646 * 2 ^ 59
def prefixEnd_55646 : Nat := 4983230072969 + 3 ^ 40 * 55646 * 2
def baseEnd_55646 : Nat := 19048763000129678979397

theorem tailTrace_55646 : CollatzResearch.WordTrace tailWord_55646 prefixEnd_55646 19048763000129678979397 := by
  unfold tailWord_55646
  simp only [CollatzResearch.WordTrace]
  refine ⟨253697044551440053161349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1353050904274346950193861 253697044551440053161349)
  ·
    refine ⟨47568195853395009967753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253697044551440053161349 47568195853395009967753)
    ·
      refine ⟨35676146890046257475815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47568195853395009967753 35676146890046257475815)
      ·
        refine ⟨53514220335069386213723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35676146890046257475815 53514220335069386213723)
        ·
          refine ⟨80271330502604079320585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53514220335069386213723 80271330502604079320585)
          ·
            refine ⟨60203497876953059490439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80271330502604079320585 60203497876953059490439)
            ·
              refine ⟨90305246815429589235659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60203497876953059490439 90305246815429589235659)
              ·
                refine ⟨135457870223144383853489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90305246815429589235659 135457870223144383853489)
                ·
                  refine ⟨101593402667358287890117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135457870223144383853489 101593402667358287890117)
                  ·
                    refine ⟨19048763000129678979397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101593402667358287890117 19048763000129678979397)
                    ·
                      rfl

theorem cell22_55646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_55646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55646 prefixEnd_55646 := by exact prefixLift 55646
  have htrace : WordTrace (prefixWord ++ tailWord_55646) baseStart_55646 baseEnd_55646 := by
    simpa [prefixWord, tailWord_55646, baseEnd_55646] using wordTrace_append hprefix tailTrace_55646
  have hstable : (prefixWord ++ tailWord_55646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55646).length < 2 ^ (prefixWord ++ tailWord_55646).sum := by decide
  have hdescent : baseEnd_55646 < baseStart_55646 := by decide
  rcases family_descends (prefixWord ++ tailWord_55646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55651 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_55651 : Nat := 118140960795 + 55651 * 2 ^ 59
def prefixEnd_55651 : Nat := 4983230072969 + 3 ^ 40 * 55651 * 2
def baseEnd_55651 : Nat := 19050474602311332604381

theorem tailTrace_55651 : CollatzResearch.WordTrace tailWord_55651 prefixEnd_55651 19050474602311332604381 := by
  unfold tailWord_55651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029758721393406279222807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1353172480928937519481871 2029758721393406279222807)
  ·
    refine ⟨3044638082090109418834211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2029758721393406279222807 3044638082090109418834211)
    ·
      refine ⟨4566957123135164128251317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044638082090109418834211 4566957123135164128251317)
      ·
        refine ⟨428152230293921637023561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4566957123135164128251317 428152230293921637023561)
        ·
          refine ⟨321114172720441227767671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428152230293921637023561 321114172720441227767671)
          ·
            refine ⟨481671259080661841651507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321114172720441227767671 481671259080661841651507)
            ·
              refine ⟨722506888620992762477261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481671259080661841651507 722506888620992762477261)
              ·
                refine ⟨270940083232872285928973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722506888620992762477261 270940083232872285928973)
                ·
                  refine ⟨101602531212327107223365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270940083232872285928973 101602531212327107223365)
                  ·
                    refine ⟨19050474602311332604381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101602531212327107223365 19050474602311332604381)
                    ·
                      rfl

theorem cell22_55651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_55651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55651 prefixEnd_55651 := by exact prefixLift 55651
  have htrace : WordTrace (prefixWord ++ tailWord_55651) baseStart_55651 baseEnd_55651 := by
    simpa [prefixWord, tailWord_55651, baseEnd_55651] using wordTrace_append hprefix tailTrace_55651
  have hstable : (prefixWord ++ tailWord_55651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55651).length < 2 ^ (prefixWord ++ tailWord_55651).sum := by decide
  have hdescent : baseEnd_55651 < baseStart_55651 := by decide
  rcases family_descends (prefixWord ++ tailWord_55651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55683 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 6]
def baseStart_55683 : Nat := 118140960795 + 55683 * 2 ^ 59
def prefixEnd_55683 : Nat := 4983230072969 + 3 ^ 40 * 55683 * 2
def baseEnd_55683 : Nat := 6353809618757971934761

theorem tailTrace_55683 : CollatzResearch.WordTrace tailWord_55683 prefixEnd_55683 6353809618757971934761 := by
  unfold tailWord_55683
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030925857277475744387703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1353950571518317162925135 2030925857277475744387703)
  ·
    refine ⟨3046388785916213616581555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030925857277475744387703 3046388785916213616581555)
    ·
      refine ⟨4569583178874320424872333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046388785916213616581555 4569583178874320424872333)
      ·
        refine ⟨1713593692077870159327125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4569583178874320424872333 1713593692077870159327125)
        ·
          refine ⟨80324704316150163718459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1713593692077870159327125 80324704316150163718459)
          ·
            refine ⟨120487056474225245577689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80324704316150163718459 120487056474225245577689)
            ·
              refine ⟨90365292355668934183267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120487056474225245577689 90365292355668934183267)
              ·
                refine ⟨135547938533503401274901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90365292355668934183267 135547938533503401274901)
                ·
                  refine ⟨6353809618757971934761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135547938533503401274901 6353809618757971934761)
                  ·
                    rfl

theorem cell22_55683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_55683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55683 prefixEnd_55683 := by exact prefixLift 55683
  have htrace : WordTrace (prefixWord ++ tailWord_55683) baseStart_55683 baseEnd_55683 := by
    simpa [prefixWord, tailWord_55683, baseEnd_55683] using wordTrace_append hprefix tailTrace_55683
  have hstable : (prefixWord ++ tailWord_55683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55683).length < 2 ^ (prefixWord ++ tailWord_55683).sum := by decide
  have hdescent : baseEnd_55683 < baseStart_55683 := by decide
  rcases family_descends (prefixWord ++ tailWord_55683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55711 : List Nat := [1, 1, 2, 5, 1, 1, 3, 8]
def baseStart_55711 : Nat := 118140960795 + 55711 * 2 ^ 59
def prefixEnd_55711 : Nat := 4983230072969 + 3 ^ 40 * 55711 * 2
def baseEnd_55711 : Nat := 2119001536499019567133

theorem tailTrace_55711 : CollatzResearch.WordTrace tailWord_55711 prefixEnd_55711 2119001536499019567133 := by
  unfold tailWord_55711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031947101176036526406987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1354631400784024350937991 2031947101176036526406987)
  ·
    refine ⟨3047920651764054789610481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031947101176036526406987 3047920651764054789610481)
    ·
      refine ⟨2285940488823041092207861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3047920651764054789610481 2285940488823041092207861)
      ·
        refine ⟨214306920827160102394487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2285940488823041092207861 214306920827160102394487)
        ·
          refine ⟨321460381240740153591731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214306920827160102394487 321460381240740153591731)
          ·
            refine ⟨482190571861110230387597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321460381240740153591731 482190571861110230387597)
            ·
              refine ⟨180821464447916336395349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482190571861110230387597 180821464447916336395349)
              ·
                refine ⟨2119001536499019567133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180821464447916336395349 2119001536499019567133)
                ·
                  rfl

theorem cell22_55711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 8].length) (baseStart_55711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55711 prefixEnd_55711 := by exact prefixLift 55711
  have htrace : WordTrace (prefixWord ++ tailWord_55711) baseStart_55711 baseEnd_55711 := by
    simpa [prefixWord, tailWord_55711, baseEnd_55711] using wordTrace_append hprefix tailTrace_55711
  have hstable : (prefixWord ++ tailWord_55711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55711).length < 2 ^ (prefixWord ++ tailWord_55711).sum := by decide
  have hdescent : baseEnd_55711 < baseStart_55711 := by decide
  rcases family_descends (prefixWord ++ tailWord_55711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55790 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_55790 : Nat := 118140960795 + 55790 * 2 ^ 59
def prefixEnd_55790 : Nat := 4983230072969 + 3 ^ 40 * 55790 * 2
def baseEnd_55790 : Nat := 6366019047653767792985

theorem tailTrace_55790 : CollatzResearch.WordTrace tailWord_55790 prefixEnd_55790 6366019047653767792985 := by
  unfold tailWord_55790
  simp only [CollatzResearch.WordTrace]
  refine ⟨254353558486229127316603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1356552311926555345688549 254353558486229127316603)
  ·
    refine ⟨381530337729343690974905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254353558486229127316603 381530337729343690974905)
    ·
      refine ⟨286147753297007768231179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381530337729343690974905 286147753297007768231179)
      ·
        refine ⟨429221629945511652346769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286147753297007768231179 429221629945511652346769)
        ·
          refine ⟨321916222459133739260077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429221629945511652346769 321916222459133739260077)
          ·
            refine ⟨120718583422175152222529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321916222459133739260077 120718583422175152222529)
            ·
              refine ⟨90538937566631364166897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120718583422175152222529 90538937566631364166897)
              ·
                refine ⟨67904203174973523125173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90538937566631364166897 67904203174973523125173)
                ·
                  refine ⟨6366019047653767792985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67904203174973523125173 6366019047653767792985)
                  ·
                    rfl

theorem cell22_55790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_55790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55790 prefixEnd_55790 := by exact prefixLift 55790
  have htrace : WordTrace (prefixWord ++ tailWord_55790) baseStart_55790 baseEnd_55790 := by
    simpa [prefixWord, tailWord_55790, baseEnd_55790] using wordTrace_append hprefix tailTrace_55790
  have hstable : (prefixWord ++ tailWord_55790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55790).length < 2 ^ (prefixWord ++ tailWord_55790).sum := by decide
  have hdescent : baseEnd_55790 < baseStart_55790 := by decide
  rcases family_descends (prefixWord ++ tailWord_55790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55794 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_55794 : Nat := 118140960795 + 55794 * 2 ^ 59
def prefixEnd_55794 : Nat := 4983230072969 + 3 ^ 40 * 55794 * 2
def baseEnd_55794 : Nat := 19099426424706626278943

theorem tailTrace_55794 : CollatzResearch.WordTrace tailWord_55794 prefixEnd_55794 19099426424706626278943 := by
  unfold tailWord_55794
  simp only [CollatzResearch.WordTrace]
  refine ⟨508743589968835425419609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1356649573250227801118957 508743589968835425419609)
  ·
    refine ⟨381557692476626569064707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 508743589968835425419609 381557692476626569064707)
    ·
      refine ⟨572336538714939853597061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381557692476626569064707 572336538714939853597061)
      ·
        refine ⟨107313101009051222549449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572336538714939853597061 107313101009051222549449)
        ·
          refine ⟨80484825756788416912087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107313101009051222549449 80484825756788416912087)
          ·
            refine ⟨120727238635182625368131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80484825756788416912087 120727238635182625368131)
            ·
              refine ⟨181090857952773938052197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120727238635182625368131 181090857952773938052197)
              ·
                refine ⟨33954535866145113384787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181090857952773938052197 33954535866145113384787)
                ·
                  refine ⟨50931803799217670077181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33954535866145113384787 50931803799217670077181)
                  ·
                    refine ⟨19099426424706626278943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50931803799217670077181 19099426424706626278943)
                    ·
                      rfl

theorem cell22_55794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_55794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55794 prefixEnd_55794 := by exact prefixLift 55794
  have htrace : WordTrace (prefixWord ++ tailWord_55794) baseStart_55794 baseEnd_55794 := by
    simpa [prefixWord, tailWord_55794, baseEnd_55794] using wordTrace_append hprefix tailTrace_55794
  have hstable : (prefixWord ++ tailWord_55794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55794).length < 2 ^ (prefixWord ++ tailWord_55794).sum := by decide
  have hdescent : baseEnd_55794 < baseStart_55794 := by decide
  rcases family_descends (prefixWord ++ tailWord_55794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55818 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_55818 : Nat := 118140960795 + 55818 * 2 ^ 59
def prefixEnd_55818 : Nat := 4983230072969 + 3 ^ 40 * 55818 * 2
def baseEnd_55818 : Nat := 6369214038392854559623

theorem tailTrace_55818 : CollatzResearch.WordTrace tailWord_55818 prefixEnd_55818 6369214038392854559623 := by
  unfold tailWord_55818
  simp only [CollatzResearch.WordTrace]
  refine ⟨508962427947098450138027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1357233141192262533701405 508962427947098450138027)
  ·
    refine ⟨763443641920647675207041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508962427947098450138027 763443641920647675207041)
    ·
      refine ⟨572582731440485756405281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763443641920647675207041 572582731440485756405281)
      ·
        refine ⟨429437048580364317303961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572582731440485756405281 429437048580364317303961)
        ·
          refine ⟨322077786435273237977971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429437048580364317303961 322077786435273237977971)
          ·
            refine ⟨483116679652909856966957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322077786435273237977971 483116679652909856966957)
            ·
              refine ⟨181168754869841196362609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483116679652909856966957 181168754869841196362609)
              ·
                refine ⟨135876566152380897271957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181168754869841196362609 135876566152380897271957)
                ·
                  refine ⟨6369214038392854559623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135876566152380897271957 6369214038392854559623)
                  ·
                    rfl

theorem cell22_55818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_55818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55818 prefixEnd_55818 := by exact prefixLift 55818
  have htrace : WordTrace (prefixWord ++ tailWord_55818) baseStart_55818 baseEnd_55818 := by
    simpa [prefixWord, tailWord_55818, baseEnd_55818] using wordTrace_append hprefix tailTrace_55818
  have hstable : (prefixWord ++ tailWord_55818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55818).length < 2 ^ (prefixWord ++ tailWord_55818).sum := by decide
  have hdescent : baseEnd_55818 < baseStart_55818 := by decide
  rcases family_descends (prefixWord ++ tailWord_55818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55833 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_55833 : Nat := 118140960795 + 55833 * 2 ^ 59
def prefixEnd_55833 : Nat := 4983230072969 + 3 ^ 40 * 55833 * 2
def baseEnd_55833 : Nat := 19112776921723524553823

theorem tailTrace_55833 : CollatzResearch.WordTrace tailWord_55833 prefixEnd_55833 19112776921723524553823 := by
  unfold tailWord_55833
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036396806734051362348153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357597871156034241565435 2036396806734051362348153)
  ·
    refine ⟨1527297605050538521761115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2036396806734051362348153 1527297605050538521761115)
    ·
      refine ⟨2290946407575807782641673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527297605050538521761115 2290946407575807782641673)
      ·
        refine ⟨1718209805681855836981255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2290946407575807782641673 1718209805681855836981255)
        ·
          refine ⟨2577314708522783755471883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718209805681855836981255 2577314708522783755471883)
          ·
            refine ⟨3865972062784175633207825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577314708522783755471883 3865972062784175633207825)
            ·
              refine ⟨2899479047088131724905869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3865972062784175633207825 2899479047088131724905869)
              ·
                refine ⟨1087304642658049396839701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899479047088131724905869 1087304642658049396839701)
                ·
                  refine ⟨50967405124596065476861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1087304642658049396839701 50967405124596065476861)
                  ·
                    refine ⟨19112776921723524553823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50967405124596065476861 19112776921723524553823)
                    ·
                      rfl

theorem cell22_55833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_55833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55833 prefixEnd_55833 := by exact prefixLift 55833
  have htrace : WordTrace (prefixWord ++ tailWord_55833) baseStart_55833 baseEnd_55833 := by
    simpa [prefixWord, tailWord_55833, baseEnd_55833] using wordTrace_append hprefix tailTrace_55833
  have hstable : (prefixWord ++ tailWord_55833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55833).length < 2 ^ (prefixWord ++ tailWord_55833).sum := by decide
  have hdescent : baseEnd_55833 < baseStart_55833 := by decide
  rcases family_descends (prefixWord ++ tailWord_55833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55837 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_55837 : Nat := 118140960795 + 55837 * 2 ^ 59
def prefixEnd_55837 : Nat := 4983230072969 + 3 ^ 40 * 55837 * 2
def baseEnd_55837 : Nat := 19114146203468847453811

theorem tailTrace_55837 : CollatzResearch.WordTrace tailWord_55837 prefixEnd_55837 19114146203468847453811 := by
  unfold tailWord_55837
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036542698719560045493765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1357695132479706696995843 2036542698719560045493765)
  ·
    refine ⟨381851756009917508530081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2036542698719560045493765 381851756009917508530081)
    ·
      refine ⟨286388817007438131397561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381851756009917508530081 286388817007438131397561)
      ·
        refine ⟨214791612755578598548171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286388817007438131397561 214791612755578598548171)
        ·
          refine ⟨322187419133367897822257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214791612755578598548171 322187419133367897822257)
          ·
            refine ⟨241640564350025923366693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322187419133367897822257 241640564350025923366693)
            ·
              refine ⟨45307605815629860631255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241640564350025923366693 45307605815629860631255)
              ·
                refine ⟨67961408723444790946883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45307605815629860631255 67961408723444790946883)
                ·
                  refine ⟨101942113085167186420325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67961408723444790946883 101942113085167186420325)
                  ·
                    refine ⟨19114146203468847453811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101942113085167186420325 19114146203468847453811)
                    ·
                      rfl

theorem cell22_55837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_55837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55837 prefixEnd_55837 := by exact prefixLift 55837
  have htrace : WordTrace (prefixWord ++ tailWord_55837) baseStart_55837 baseEnd_55837 := by
    simpa [prefixWord, tailWord_55837, baseEnd_55837] using wordTrace_append hprefix tailTrace_55837
  have hstable : (prefixWord ++ tailWord_55837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55837).length < 2 ^ (prefixWord ++ tailWord_55837).sum := by decide
  have hdescent : baseEnd_55837 < baseStart_55837 := by decide
  rcases family_descends (prefixWord ++ tailWord_55837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55908 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_55908 : Nat := 118140960795 + 55908 * 2 ^ 59
def prefixEnd_55908 : Nat := 4983230072969 + 3 ^ 40 * 55908 * 2
def baseEnd_55908 : Nat := 6379483651482776309531

theorem tailTrace_55908 : CollatzResearch.WordTrace tailWord_55908 prefixEnd_55908 6379483651482776309531 := by
  unfold tailWord_55908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019566140731169585664189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1359421520974892780885585 1019566140731169585664189)
  ·
    refine ⟨382337302774188594624071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1019566140731169585664189 382337302774188594624071)
    ·
      refine ⟨573505954161282891936107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382337302774188594624071 573505954161282891936107)
      ·
        refine ⟨860258931241924337904161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573505954161282891936107 860258931241924337904161)
        ·
          refine ⟨645194198431443253428121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860258931241924337904161 645194198431443253428121)
          ·
            refine ⟨483895648823582440071091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645194198431443253428121 483895648823582440071091)
            ·
              refine ⟨725843473235373660106637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483895648823582440071091 725843473235373660106637)
              ·
                refine ⟨272191302463265122539989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725843473235373660106637 272191302463265122539989)
                ·
                  refine ⟨6379483651482776309531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272191302463265122539989 6379483651482776309531)
                  ·
                    rfl

theorem cell22_55908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_55908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_55908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_55908 prefixEnd_55908 := by exact prefixLift 55908
  have htrace : WordTrace (prefixWord ++ tailWord_55908) baseStart_55908 baseEnd_55908 := by
    simpa [prefixWord, tailWord_55908, baseEnd_55908] using wordTrace_append hprefix tailTrace_55908
  have hstable : (prefixWord ++ tailWord_55908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55908).length < 2 ^ (prefixWord ++ tailWord_55908).sum := by decide
  have hdescent : baseEnd_55908 < baseStart_55908 := by decide
  rcases family_descends (prefixWord ++ tailWord_55908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56000 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_56000 : Nat := 118140960795 + 56000 * 2 ^ 59
def prefixEnd_56000 : Nat := 4983230072969 + 3 ^ 40 * 56000 * 2
def baseEnd_56000 : Nat := 19169944434590755628311

theorem tailTrace_56000 : CollatzResearch.WordTrace tailWord_56000 prefixEnd_56000 19169944434590755628311 := by
  unfold tailWord_56000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021243898564519441838727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1361658531419359255784969 1021243898564519441838727)
  ·
    refine ⟨1531865847846779162758091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1021243898564519441838727 1531865847846779162758091)
    ·
      refine ⟨2297798771770168744137137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531865847846779162758091 2297798771770168744137137)
      ·
        refine ⟨1723349078827626558102853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297798771770168744137137 1723349078827626558102853)
        ·
          refine ⟨323127952280179979644285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1723349078827626558102853 323127952280179979644285)
          ·
            refine ⟨121172982105067492366607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323127952280179979644285 121172982105067492366607)
            ·
              refine ⟨181759473157601238549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121172982105067492366607 181759473157601238549911)
              ·
                refine ⟨272639209736401857824867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181759473157601238549911 272639209736401857824867)
                ·
                  refine ⟨408958814604602786737301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272639209736401857824867 408958814604602786737301)
                  ·
                    refine ⟨19169944434590755628311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 408958814604602786737301 19169944434590755628311)
                    ·
                      rfl

theorem cell22_56000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_56000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56000 prefixEnd_56000 := by exact prefixLift 56000
  have htrace : WordTrace (prefixWord ++ tailWord_56000) baseStart_56000 baseEnd_56000 := by
    simpa [prefixWord, tailWord_56000, baseEnd_56000] using wordTrace_append hprefix tailTrace_56000
  have hstable : (prefixWord ++ tailWord_56000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56000).length < 2 ^ (prefixWord ++ tailWord_56000).sum := by decide
  have hdescent : baseEnd_56000 < baseStart_56000 := by decide
  rcases family_descends (prefixWord ++ tailWord_56000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56004 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_56004 : Nat := 118140960795 + 56004 * 2 ^ 59
def prefixEnd_56004 : Nat := 4983230072969 + 3 ^ 40 * 56004 * 2
def baseEnd_56004 : Nat := 6390437905445359509433

theorem tailTrace_56004 : CollatzResearch.WordTrace tailWord_56004 prefixEnd_56004 6390437905445359509433 := by
  unfold tailWord_56004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021316844557273783411533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1361755792743031711215377 1021316844557273783411533)
  ·
    refine ⟨382993816708977668779325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1021316844557273783411533 382993816708977668779325)
    ·
      refine ⟨143622681265866625792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 382993816708977668779325 143622681265866625792247)
      ·
        refine ⟨215434021898799938688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143622681265866625792247 215434021898799938688371)
        ·
          refine ⟨323151032848199908032557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215434021898799938688371 323151032848199908032557)
          ·
            refine ⟨121181637318074965512209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323151032848199908032557 121181637318074965512209)
            ·
              refine ⟨90886227988556224134157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121181637318074965512209 90886227988556224134157)
              ·
                refine ⟨34082335495708584050309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90886227988556224134157 34082335495708584050309)
                ·
                  refine ⟨6390437905445359509433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34082335495708584050309 6390437905445359509433)
                  ·
                    rfl

theorem cell22_56004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_56004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56004 prefixEnd_56004 := by exact prefixLift 56004
  have htrace : WordTrace (prefixWord ++ tailWord_56004) baseStart_56004 baseEnd_56004 := by
    simpa [prefixWord, tailWord_56004, baseEnd_56004] using wordTrace_append hprefix tailTrace_56004
  have hstable : (prefixWord ++ tailWord_56004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56004).length < 2 ^ (prefixWord ++ tailWord_56004).sum := by decide
  have hdescent : baseEnd_56004 < baseStart_56004 := by decide
  rcases family_descends (prefixWord ++ tailWord_56004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56047 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 3, 3]
def baseStart_56047 : Nat := 118140960795 + 56047 * 2 ^ 59
def prefixEnd_56047 : Nat := 4983230072969 + 3 ^ 40 * 56047 * 2
def baseEnd_56047 : Nat := 19186033495098299703167

theorem tailTrace_56047 : CollatzResearch.WordTrace tailWord_56047 prefixEnd_56047 19186033495098299703167 := by
  unfold tailWord_56047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044202027958765910638395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1362801351972510607092263 2044202027958765910638395)
  ·
    refine ⟨3066303041938148865957593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2044202027958765910638395 3066303041938148865957593)
    ·
      refine ⟨2299727281453611649468195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3066303041938148865957593 2299727281453611649468195)
      ·
        refine ⟨3449590922180417474202293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299727281453611649468195 3449590922180417474202293)
        ·
          refine ⟨323399148954414138206465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3449590922180417474202293 323399148954414138206465)
          ·
            refine ⟨242549361715810603654849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323399148954414138206465 242549361715810603654849)
            ·
              refine ⟨181912021286857952741137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242549361715810603654849 181912021286857952741137)
              ·
                refine ⟨136434015965143464555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181912021286857952741137 136434015965143464555853)
                ·
                  refine ⟨51162755986928799208445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136434015965143464555853 51162755986928799208445)
                  ·
                    refine ⟨19186033495098299703167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51162755986928799208445 19186033495098299703167)
                    ·
                      rfl

theorem cell22_56047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_56047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56047 prefixEnd_56047 := by exact prefixLift 56047
  have htrace : WordTrace (prefixWord ++ tailWord_56047) baseStart_56047 baseEnd_56047 := by
    simpa [prefixWord, tailWord_56047, baseEnd_56047] using wordTrace_append hprefix tailTrace_56047
  have hstable : (prefixWord ++ tailWord_56047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56047).length < 2 ^ (prefixWord ++ tailWord_56047).sum := by decide
  have hdescent : baseEnd_56047 < baseStart_56047 := by decide
  rcases family_descends (prefixWord ++ tailWord_56047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56060 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_56060 : Nat := 118140960795 + 56060 * 2 ^ 59
def prefixEnd_56060 : Nat := 4983230072969 + 3 ^ 40 * 56060 * 2
def baseEnd_56060 : Nat := 6396827886923533042709

theorem tailTrace_56060 : CollatzResearch.WordTrace tailWord_56060 prefixEnd_56060 6396827886923533042709 := by
  unfold tailWord_56060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022338088455834565430817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1363117451274446087241089 1022338088455834565430817)
  ·
    refine ⟨766753566341875924073113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1022338088455834565430817 766753566341875924073113)
    ·
      refine ⟨575065174756406943054835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766753566341875924073113 575065174756406943054835)
      ·
        refine ⟨862597762134610414582253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575065174756406943054835 862597762134610414582253)
        ·
          refine ⟨323474160800478905468345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862597762134610414582253 323474160800478905468345)
          ·
            refine ⟨242605620600359179101259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323474160800478905468345 242605620600359179101259)
            ·
              refine ⟨363908430900538768651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242605620600359179101259 363908430900538768651889)
              ·
                refine ⟨272931323175404076488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363908430900538768651889 272931323175404076488917)
                ·
                  refine ⟨6396827886923533042709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 272931323175404076488917 6396827886923533042709)
                  ·
                    rfl

theorem cell22_56060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_56060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56060 prefixEnd_56060 := by exact prefixLift 56060
  have htrace : WordTrace (prefixWord ++ tailWord_56060) baseStart_56060 baseEnd_56060 := by
    simpa [prefixWord, tailWord_56060, baseEnd_56060] using wordTrace_append hprefix tailTrace_56060
  have hstable : (prefixWord ++ tailWord_56060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56060).length < 2 ^ (prefixWord ++ tailWord_56060).sum := by decide
  have hdescent : baseEnd_56060 < baseStart_56060 := by decide
  rcases family_descends (prefixWord ++ tailWord_56060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56132 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_56132 : Nat := 118140960795 + 56132 * 2 ^ 59
def prefixEnd_56132 : Nat := 4983230072969 + 3 ^ 40 * 56132 * 2
def baseEnd_56132 : Nat := 19215130732186411327907

theorem tailTrace_56132 : CollatzResearch.WordTrace tailWord_56132 prefixEnd_56132 19215130732186411327907 := by
  unfold tailWord_56132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023651116325412713741325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1364868155100550284988433 1023651116325412713741325)
  ·
    refine ⟨383869168622029767652997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1023651116325412713741325 383869168622029767652997)
    ·
      refine ⟨71975469116630581434937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383869168622029767652997 71975469116630581434937)
      ·
        refine ⟨53981601837472936076203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71975469116630581434937 53981601837472936076203)
        ·
          refine ⟨80972402756209404114305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53981601837472936076203 80972402756209404114305)
          ·
            refine ⟨60729302067157053085729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80972402756209404114305 60729302067157053085729)
            ·
              refine ⟨45546976550367789814297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60729302067157053085729 45546976550367789814297)
              ·
                refine ⟨34160232412775842360723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45546976550367789814297 34160232412775842360723)
                ·
                  refine ⟨51240348619163763541085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34160232412775842360723 51240348619163763541085)
                  ·
                    refine ⟨19215130732186411327907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51240348619163763541085 19215130732186411327907)
                    ·
                      rfl

theorem cell22_56132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_56132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56132 prefixEnd_56132 := by exact prefixLift 56132
  have htrace : WordTrace (prefixWord ++ tailWord_56132) baseStart_56132 baseEnd_56132 := by
    simpa [prefixWord, tailWord_56132, baseEnd_56132] using wordTrace_append hprefix tailTrace_56132
  have hstable : (prefixWord ++ tailWord_56132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56132).length < 2 ^ (prefixWord ++ tailWord_56132).sum := by decide
  have hdescent : baseEnd_56132 < baseStart_56132 := by decide
  rcases family_descends (prefixWord ++ tailWord_56132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56135 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_56135 : Nat := 118140960795 + 56135 * 2 ^ 59
def prefixEnd_56135 : Nat := 4983230072969 + 3 ^ 40 * 56135 * 2
def baseEnd_56135 : Nat := 19216157693495403502897

theorem tailTrace_56135 : CollatzResearch.WordTrace tailWord_56135 prefixEnd_56135 19216157693495403502897 := by
  unfold tailWord_56135
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047411651639956939841859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1364941101093304626561239 2047411651639956939841859)
  ·
    refine ⟨3071117477459935409762789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047411651639956939841859 3071117477459935409762789)
    ·
      refine ⟨575834527023737889330523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3071117477459935409762789 575834527023737889330523)
      ·
        refine ⟨863751790535606833995785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575834527023737889330523 863751790535606833995785)
        ·
          refine ⟨647813842901705125496839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863751790535606833995785 647813842901705125496839)
          ·
            refine ⟨971720764352557688245259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647813842901705125496839 971720764352557688245259)
            ·
              refine ⟨1457581146528836532367889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971720764352557688245259 1457581146528836532367889)
              ·
                refine ⟨1093185859896627399275917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457581146528836532367889 1093185859896627399275917)
                ·
                  refine ⟨409944697461235274728469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093185859896627399275917 409944697461235274728469)
                  ·
                    refine ⟨19216157693495403502897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 409944697461235274728469 19216157693495403502897)
                    ·
                      rfl

theorem cell22_56135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_56135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56135 prefixEnd_56135 := by exact prefixLift 56135
  have htrace : WordTrace (prefixWord ++ tailWord_56135) baseStart_56135 baseEnd_56135 := by
    simpa [prefixWord, tailWord_56135, baseEnd_56135] using wordTrace_append hprefix tailTrace_56135
  have hstable : (prefixWord ++ tailWord_56135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56135).length < 2 ^ (prefixWord ++ tailWord_56135).sum := by decide
  have hdescent : baseEnd_56135 < baseStart_56135 := by decide
  rcases family_descends (prefixWord ++ tailWord_56135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56154 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_56154 : Nat := 118140960795 + 56154 * 2 ^ 59
def prefixEnd_56154 : Nat := 4983230072969 + 3 ^ 40 * 56154 * 2
def baseEnd_56154 : Nat := 19222661781785687277839

theorem tailTrace_56154 : CollatzResearch.WordTrace tailWord_56154 prefixEnd_56154 19222661781785687277839 := by
  unfold tailWord_56154
  simp only [CollatzResearch.WordTrace]
  refine ⟨512026159642780796195879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1365403092380748789855677 512026159642780796195879)
  ·
    refine ⟨768039239464171194293819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512026159642780796195879 768039239464171194293819)
    ·
      refine ⟨1152058859196256791440729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768039239464171194293819 1152058859196256791440729)
      ·
        refine ⟨864044144397192593580547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152058859196256791440729 864044144397192593580547)
        ·
          refine ⟨1296066216595788890370821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864044144397192593580547 1296066216595788890370821)
          ·
            refine ⟨243012415611710416944529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1296066216595788890370821 243012415611710416944529)
            ·
              refine ⟨182259311708782812708397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243012415611710416944529 182259311708782812708397)
              ·
                refine ⟨68347241890793554765649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182259311708782812708397 68347241890793554765649)
                ·
                  refine ⟨51260431418095166074237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68347241890793554765649 51260431418095166074237)
                  ·
                    refine ⟨19222661781785687277839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51260431418095166074237 19222661781785687277839)
                    ·
                      rfl

theorem cell22_56154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_56154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56154 prefixEnd_56154 := by exact prefixLift 56154
  have htrace : WordTrace (prefixWord ++ tailWord_56154) baseStart_56154 baseEnd_56154 := by
    simpa [prefixWord, tailWord_56154, baseEnd_56154] using wordTrace_append hprefix tailTrace_56154
  have hstable : (prefixWord ++ tailWord_56154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56154).length < 2 ^ (prefixWord ++ tailWord_56154).sum := by decide
  have hdescent : baseEnd_56154 < baseStart_56154 := by decide
  rcases family_descends (prefixWord ++ tailWord_56154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56199 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 3, 3]
def baseStart_56199 : Nat := 118140960795 + 56199 * 2 ^ 59
def prefixEnd_56199 : Nat := 4983230072969 + 3 ^ 40 * 56199 * 2
def baseEnd_56199 : Nat := 19238066201420569902701

theorem tailTrace_56199 : CollatzResearch.WordTrace tailWord_56199 prefixEnd_56199 19238066201420569902701 := by
  unfold tailWord_56199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049745923408095870171651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1366497282272063913447767 2049745923408095870171651)
  ·
    refine ⟨3074618885112143805257477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049745923408095870171651 3074618885112143805257477)
    ·
      refine ⟨576491040958526963485777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3074618885112143805257477 576491040958526963485777)
      ·
        refine ⟨432368280718895222614333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576491040958526963485777 432368280718895222614333)
        ·
          refine ⟨162138105269585708480375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432368280718895222614333 162138105269585708480375)
          ·
            refine ⟨243207157904378562720563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162138105269585708480375 243207157904378562720563)
            ·
              refine ⟨364810736856567844080845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243207157904378562720563 364810736856567844080845)
              ·
                refine ⟨136804026321212941530317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364810736856567844080845 136804026321212941530317)
                ·
                  refine ⟨51301509870454853073869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136804026321212941530317 51301509870454853073869)
                  ·
                    refine ⟨19238066201420569902701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51301509870454853073869 19238066201420569902701)
                    ·
                      rfl

theorem cell22_56199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_56199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56199 prefixEnd_56199 := by exact prefixLift 56199
  have htrace : WordTrace (prefixWord ++ tailWord_56199) baseStart_56199 baseEnd_56199 := by
    simpa [prefixWord, tailWord_56199, baseEnd_56199] using wordTrace_append hprefix tailTrace_56199
  have hstable : (prefixWord ++ tailWord_56199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56199).length < 2 ^ (prefixWord ++ tailWord_56199).sum := by decide
  have hdescent : baseEnd_56199 < baseStart_56199 := by decide
  rcases family_descends (prefixWord ++ tailWord_56199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56242 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_56242 : Nat := 118140960795 + 56242 * 2 ^ 59
def prefixEnd_56242 : Nat := 4983230072969 + 3 ^ 40 * 56242 * 2
def baseEnd_56242 : Nat := 19252785980182791077569

theorem tailTrace_56242 : CollatzResearch.WordTrace tailWord_56242 prefixEnd_56242 19252785980182791077569 := by
  unfold tailWord_56242
  simp only [CollatzResearch.WordTrace]
  refine ⟨512828565563078553496745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1367542841501542809324653 512828565563078553496745)
  ·
    refine ⟨384621424172308915122559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 512828565563078553496745 384621424172308915122559)
    ·
      refine ⟨576932136258463372683839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384621424172308915122559 576932136258463372683839)
      ·
        refine ⟨865398204387695059025759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576932136258463372683839 865398204387695059025759)
        ·
          refine ⟨1298097306581542588538639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865398204387695059025759 1298097306581542588538639)
          ·
            refine ⟨1947145959872313882807959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298097306581542588538639 1947145959872313882807959)
            ·
              refine ⟨2920718939808470824211939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1947145959872313882807959 2920718939808470824211939)
              ·
                refine ⟨4381078409712706236317909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920718939808470824211939 4381078409712706236317909)
                ·
                  refine ⟨102681525227641552413701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4381078409712706236317909 102681525227641552413701)
                  ·
                    refine ⟨19252785980182791077569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102681525227641552413701 19252785980182791077569)
                    ·
                      rfl

theorem cell22_56242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_56242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56242 prefixEnd_56242 := by exact prefixLift 56242
  have htrace : WordTrace (prefixWord ++ tailWord_56242) baseStart_56242 baseEnd_56242 := by
    simpa [prefixWord, tailWord_56242, baseEnd_56242] using wordTrace_append hprefix tailTrace_56242
  have hstable : (prefixWord ++ tailWord_56242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56242).length < 2 ^ (prefixWord ++ tailWord_56242).sum := by decide
  have hdescent : baseEnd_56242 < baseStart_56242 := by decide
  rcases family_descends (prefixWord ++ tailWord_56242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56272 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_56272 : Nat := 118140960795 + 56272 * 2 ^ 59
def prefixEnd_56272 : Nat := 4983230072969 + 3 ^ 40 * 56272 * 2
def baseEnd_56272 : Nat := 19263055593272712827477

theorem tailTrace_56272 : CollatzResearch.WordTrace tailWord_56272 prefixEnd_56272 19263055593272712827477 := by
  unfold tailWord_56272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026204226071814668789535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1368272301429086225052713 1026204226071814668789535)
  ·
    refine ⟨1539306339107722003184303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1026204226071814668789535 1539306339107722003184303)
    ·
      refine ⟨2308959508661583004776455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539306339107722003184303 2308959508661583004776455)
      ·
        refine ⟨3463439262992374507164683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308959508661583004776455 3463439262992374507164683)
        ·
          refine ⟨5195158894488561760747025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463439262992374507164683 5195158894488561760747025)
          ·
            refine ⟨3896369170866421320560269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5195158894488561760747025 3896369170866421320560269)
            ·
              refine ⟨1461138439074907995210101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896369170866421320560269 1461138439074907995210101)
              ·
                refine ⟨136981728663272624550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1461138439074907995210101 136981728663272624550947)
                ·
                  refine ⟨205472592994908936826421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136981728663272624550947 205472592994908936826421)
                  ·
                    refine ⟨19263055593272712827477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 205472592994908936826421 19263055593272712827477)
                    ·
                      rfl

theorem cell22_56272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_56272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56272 prefixEnd_56272 := by exact prefixLift 56272
  have htrace : WordTrace (prefixWord ++ tailWord_56272) baseStart_56272 baseEnd_56272 := by
    simpa [prefixWord, tailWord_56272, baseEnd_56272] using wordTrace_append hprefix tailTrace_56272
  have hstable : (prefixWord ++ tailWord_56272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56272).length < 2 ^ (prefixWord ++ tailWord_56272).sum := by decide
  have hdescent : baseEnd_56272 < baseStart_56272 := by decide
  rcases family_descends (prefixWord ++ tailWord_56272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56276 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_56276 : Nat := 118140960795 + 56276 * 2 ^ 59
def prefixEnd_56276 : Nat := 4983230072969 + 3 ^ 40 * 56276 * 2
def baseEnd_56276 : Nat := 19264424875018035727465

theorem tailTrace_56276 : CollatzResearch.WordTrace tailWord_56276 prefixEnd_56276 19264424875018035727465 := by
  unfold tailWord_56276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026277172064569010362341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1368369562752758680483121 1026277172064569010362341)
  ·
    refine ⟨192426969762106689442939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1026277172064569010362341 192426969762106689442939)
    ·
      refine ⟨288640454643160034164409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192426969762106689442939 288640454643160034164409)
      ·
        refine ⟨216480340982370025623307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288640454643160034164409 216480340982370025623307)
        ·
          refine ⟨324720511473555038434961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216480340982370025623307 324720511473555038434961)
          ·
            refine ⟨243540383605166278826221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324720511473555038434961 243540383605166278826221)
            ·
              refine ⟨91327643851937354559833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243540383605166278826221 91327643851937354559833)
              ·
                refine ⟨68495732888953015919875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91327643851937354559833 68495732888953015919875)
                ·
                  refine ⟨102743599333429523879813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68495732888953015919875 102743599333429523879813)
                  ·
                    refine ⟨19264424875018035727465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102743599333429523879813 19264424875018035727465)
                    ·
                      rfl

theorem cell22_56276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_56276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56276 prefixEnd_56276 := by exact prefixLift 56276
  have htrace : WordTrace (prefixWord ++ tailWord_56276) baseStart_56276 baseEnd_56276 := by
    simpa [prefixWord, tailWord_56276, baseEnd_56276] using wordTrace_append hprefix tailTrace_56276
  have hstable : (prefixWord ++ tailWord_56276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56276).length < 2 ^ (prefixWord ++ tailWord_56276).sum := by decide
  have hdescent : baseEnd_56276 < baseStart_56276 := by decide
  rcases family_descends (prefixWord ++ tailWord_56276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56302 : List Nat := [4, 1, 2, 1, 14]
def baseStart_56302 : Nat := 118140960795 + 56302 * 2 ^ 59
def prefixEnd_56302 : Nat := 4983230072969 + 3 ^ 40 * 56302 * 2
def baseEnd_56302 : Nat := 79314095499434710195

theorem tailTrace_56302 : CollatzResearch.WordTrace tailWord_56302 prefixEnd_56302 79314095499434710195 := by
  unfold tailWord_56302
  simp only [CollatzResearch.WordTrace]
  refine ⟨256687830254368057646395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1369001761356629640780773 256687830254368057646395)
  ·
    refine ⟨385031745381552086469593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256687830254368057646395 385031745381552086469593)
    ·
      refine ⟨288773809036164064852195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385031745381552086469593 288773809036164064852195)
      ·
        refine ⟨433160713554246097278293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288773809036164064852195 433160713554246097278293)
        ·
          refine ⟨79314095499434710195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 433160713554246097278293 79314095499434710195)
          ·
            rfl

theorem cell22_56302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 14].length) (baseStart_56302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56302 prefixEnd_56302 := by exact prefixLift 56302
  have htrace : WordTrace (prefixWord ++ tailWord_56302) baseStart_56302 baseEnd_56302 := by
    simpa [prefixWord, tailWord_56302, baseEnd_56302] using wordTrace_append hprefix tailTrace_56302
  have hstable : (prefixWord ++ tailWord_56302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56302).length < 2 ^ (prefixWord ++ tailWord_56302).sum := by decide
  have hdescent : baseEnd_56302 < baseStart_56302 := by decide
  rcases family_descends (prefixWord ++ tailWord_56302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56317 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_56317 : Nat := 118140960795 + 56317 * 2 ^ 59
def prefixEnd_56317 : Nat := 4983230072969 + 3 ^ 40 * 56317 * 2
def baseEnd_56317 : Nat := 19278460012907595452339

theorem tailTrace_56317 : CollatzResearch.WordTrace tailWord_56317 prefixEnd_56317 19278460012907595452339 := by
  unfold tailWord_56317
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054049736980602022967205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1369366491320401348644803 2054049736980602022967205)
  ·
    refine ⟨385134325683862879306351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2054049736980602022967205 385134325683862879306351)
    ·
      refine ⟨577701488525794318959527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385134325683862879306351 577701488525794318959527)
      ·
        refine ⟨866552232788691478439291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577701488525794318959527 866552232788691478439291)
        ·
          refine ⟨1299828349183037217658937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866552232788691478439291 1299828349183037217658937)
          ·
            refine ⟨974871261887277913244203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299828349183037217658937 974871261887277913244203)
            ·
              refine ⟨1462306892830916869866305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974871261887277913244203 1462306892830916869866305)
              ·
                refine ⟨1096730169623187652399729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462306892830916869866305 1096730169623187652399729)
                ·
                  refine ⟨822547627217390739299797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1096730169623187652399729 822547627217390739299797)
                  ·
                    refine ⟨19278460012907595452339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 822547627217390739299797 19278460012907595452339)
                    ·
                      rfl

theorem cell22_56317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_56317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56317 prefixEnd_56317 := by exact prefixLift 56317
  have htrace : WordTrace (prefixWord ++ tailWord_56317) baseStart_56317 baseEnd_56317 := by
    simpa [prefixWord, tailWord_56317, baseEnd_56317] using wordTrace_append hprefix tailTrace_56317
  have hstable : (prefixWord ++ tailWord_56317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56317).length < 2 ^ (prefixWord ++ tailWord_56317).sum := by decide
  have hdescent : baseEnd_56317 < baseStart_56317 := by decide
  rcases family_descends (prefixWord ++ tailWord_56317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56394 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_56394 : Nat := 118140960795 + 56394 * 2 ^ 59
def prefixEnd_56394 : Nat := 4983230072969 + 3 ^ 40 * 56394 * 2
def baseEnd_56394 : Nat := 19304818686505061277103

theorem tailTrace_56394 : CollatzResearch.WordTrace tailWord_56394 prefixEnd_56394 19304818686505061277103 := by
  unfold tailWord_56394
  simp only [CollatzResearch.WordTrace]
  refine ⟨514214539425411043380059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1371238771801096115680157 514214539425411043380059)
  ·
    refine ⟨771321809138116565070089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514214539425411043380059 771321809138116565070089)
    ·
      refine ⟨578491356853587423802567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 771321809138116565070089 578491356853587423802567)
      ·
        refine ⟨867737035280381135703851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578491356853587423802567 867737035280381135703851)
        ·
          refine ⟨1301605552920571703555777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867737035280381135703851 1301605552920571703555777)
          ·
            refine ⟨976204164690428777666833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301605552920571703555777 976204164690428777666833)
            ·
              refine ⟨732153123517821583250125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976204164690428777666833 732153123517821583250125)
              ·
                refine ⟨274557421319183093718797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732153123517821583250125 274557421319183093718797)
                ·
                  refine ⟨102959032994693660144549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274557421319183093718797 102959032994693660144549)
                  ·
                    refine ⟨19304818686505061277103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102959032994693660144549 19304818686505061277103)
                    ·
                      rfl

theorem cell22_56394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_56394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56394 prefixEnd_56394 := by exact prefixLift 56394
  have htrace : WordTrace (prefixWord ++ tailWord_56394) baseStart_56394 baseEnd_56394 := by
    simpa [prefixWord, tailWord_56394, baseEnd_56394] using wordTrace_append hprefix tailTrace_56394
  have hstable : (prefixWord ++ tailWord_56394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56394).length < 2 ^ (prefixWord ++ tailWord_56394).sum := by decide
  have hdescent : baseEnd_56394 < baseStart_56394 := by decide
  rcases family_descends (prefixWord ++ tailWord_56394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56426 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_56426 : Nat := 118140960795 + 56426 * 2 ^ 59
def prefixEnd_56426 : Nat := 4983230072969 + 3 ^ 40 * 56426 * 2
def baseEnd_56426 : Nat := 6438590980155881492335

theorem tailTrace_56426 : CollatzResearch.WordTrace tailWord_56426 prefixEnd_56426 6438590980155881492335 := by
  unfold tailWord_56426
  simp only [CollatzResearch.WordTrace]
  refine ⟨514506323396428409671283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1372016862390475759123421 514506323396428409671283)
  ·
    refine ⟨771759485094642614506925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514506323396428409671283 771759485094642614506925)
    ·
      refine ⟨289409806910490980440097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 771759485094642614506925 289409806910490980440097)
      ·
        refine ⟨217057355182868235330073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289409806910490980440097 217057355182868235330073)
        ·
          refine ⟨162793016387151176497555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217057355182868235330073 162793016387151176497555)
          ·
            refine ⟨244189524580726764746333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162793016387151176497555 244189524580726764746333)
            ·
              refine ⟨91571071717772536779875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244189524580726764746333 91571071717772536779875)
              ·
                refine ⟨137356607576658805169813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91571071717772536779875 137356607576658805169813)
                ·
                  refine ⟨6438590980155881492335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137356607576658805169813 6438590980155881492335)
                  ·
                    rfl

theorem cell22_56426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_56426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56426 prefixEnd_56426 := by exact prefixLift 56426
  have htrace : WordTrace (prefixWord ++ tailWord_56426) baseStart_56426 baseEnd_56426 := by
    simpa [prefixWord, tailWord_56426, baseEnd_56426] using wordTrace_append hprefix tailTrace_56426
  have hstable : (prefixWord ++ tailWord_56426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56426).length < 2 ^ (prefixWord ++ tailWord_56426).sum := by decide
  have hdescent : baseEnd_56426 < baseStart_56426 := by decide
  rcases family_descends (prefixWord ++ tailWord_56426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56439 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_56439 : Nat := 118140960795 + 56439 * 2 ^ 59
def prefixEnd_56439 : Nat := 4983230072969 + 3 ^ 40 * 56439 * 2
def baseEnd_56439 : Nat := 19320223106139943901965

theorem tailTrace_56439 : CollatzResearch.WordTrace tailWord_56439 prefixEnd_56439 19320223106139943901965 := by
  unfold tailWord_56439
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058499442538616858908371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1372332961692411239272247 2058499442538616858908371)
  ·
    refine ⟨3087749163807925288362557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058499442538616858908371 3087749163807925288362557)
    ·
      refine ⟨1157905936427971983135959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3087749163807925288362557 1157905936427971983135959)
      ·
        refine ⟨1736858904641957974703939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1157905936427971983135959 1736858904641957974703939)
        ·
          refine ⟨2605288356962936962055909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736858904641957974703939 2605288356962936962055909)
          ·
            refine ⟨488491566930550680385483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2605288356962936962055909 488491566930550680385483)
            ·
              refine ⟨732737350395826020578225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488491566930550680385483 732737350395826020578225)
              ·
                refine ⟨549553012796869515433669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732737350395826020578225 549553012796869515433669)
                ·
                  refine ⟨103041189899413034143813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549553012796869515433669 103041189899413034143813)
                  ·
                    refine ⟨19320223106139943901965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103041189899413034143813 19320223106139943901965)
                    ·
                      rfl

theorem cell22_56439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_56439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56439 prefixEnd_56439 := by exact prefixLift 56439
  have htrace : WordTrace (prefixWord ++ tailWord_56439) baseStart_56439 baseEnd_56439 := by
    simpa [prefixWord, tailWord_56439, baseEnd_56439] using wordTrace_append hprefix tailTrace_56439
  have hstable : (prefixWord ++ tailWord_56439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56439).length < 2 ^ (prefixWord ++ tailWord_56439).sum := by decide
  have hdescent : baseEnd_56439 < baseStart_56439 := by decide
  rcases family_descends (prefixWord ++ tailWord_56439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56533 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 5]
def baseStart_56533 : Nat := 118140960795 + 56533 * 2 ^ 59
def prefixEnd_56533 : Nat := 4983230072969 + 3 ^ 40 * 56533 * 2
def baseEnd_56533 : Nat := 6450800409051677350559

theorem tailTrace_56533 : CollatzResearch.WordTrace tailWord_56533 prefixEnd_56533 6450800409051677350559 := by
  unfold tailWord_56533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061927904198070912830253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1374618602798713941886835 2061927904198070912830253)
  ·
    refine ⟨773222964074276592311345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2061927904198070912830253 773222964074276592311345)
    ·
      refine ⟨579917223055707444233509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773222964074276592311345 579917223055707444233509)
      ·
        refine ⟨108734479322945145793783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 579917223055707444233509 108734479322945145793783)
        ·
          refine ⟨163101718984417718690675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108734479322945145793783 163101718984417718690675)
          ·
            refine ⟨244652578476626578036013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163101718984417718690675 244652578476626578036013)
            ·
              refine ⟨91744716928734966763505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244652578476626578036013 91744716928734966763505)
              ·
                refine ⟨68808537696551225072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91744716928734966763505 68808537696551225072629)
                ·
                  refine ⟨6450800409051677350559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68808537696551225072629 6450800409051677350559)
                  ·
                    rfl

theorem cell22_56533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_56533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56533 prefixEnd_56533 := by exact prefixLift 56533
  have htrace : WordTrace (prefixWord ++ tailWord_56533) baseStart_56533 baseEnd_56533 := by
    simpa [prefixWord, tailWord_56533, baseEnd_56533] using wordTrace_append hprefix tailTrace_56533
  have hstable : (prefixWord ++ tailWord_56533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56533).length < 2 ^ (prefixWord ++ tailWord_56533).sum := by decide
  have hdescent : baseEnd_56533 < baseStart_56533 := by decide
  rcases family_descends (prefixWord ++ tailWord_56533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56563 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 1, 4]
def baseStart_56563 : Nat := 118140960795 + 56563 * 2 ^ 59
def prefixEnd_56563 : Nat := 4983230072969 + 3 ^ 40 * 56563 * 2
def baseEnd_56563 : Nat := 19362670840244953801585

theorem tailTrace_56563 : CollatzResearch.WordTrace tailWord_56563 prefixEnd_56563 19362670840244953801585 := by
  unfold tailWord_56563
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063022094089386036422343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1375348062726257357614895 2063022094089386036422343)
  ·
    refine ⟨3094533141134079054633515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063022094089386036422343 3094533141134079054633515)
    ·
      refine ⟨4641799711701118581950273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094533141134079054633515 4641799711701118581950273)
      ·
        refine ⟨3481349783775838936462705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4641799711701118581950273 3481349783775838936462705)
        ·
          refine ⟨2611012337831879202347029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481349783775838936462705 2611012337831879202347029)
          ·
            refine ⟨122391203335869337610017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2611012337831879202347029 122391203335869337610017)
            ·
              refine ⟨91793402501902003207513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122391203335869337610017 91793402501902003207513)
              ·
                refine ⟨68845051876426502405635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91793402501902003207513 68845051876426502405635)
                ·
                  refine ⟨103267577814639753608453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68845051876426502405635 103267577814639753608453)
                  ·
                    refine ⟨19362670840244953801585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103267577814639753608453 19362670840244953801585)
                    ·
                      rfl

theorem cell22_56563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_56563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56563 prefixEnd_56563 := by exact prefixLift 56563
  have htrace : WordTrace (prefixWord ++ tailWord_56563) baseStart_56563 baseEnd_56563 := by
    simpa [prefixWord, tailWord_56563, baseEnd_56563] using wordTrace_append hprefix tailTrace_56563
  have hstable : (prefixWord ++ tailWord_56563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56563).length < 2 ^ (prefixWord ++ tailWord_56563).sum := by decide
  have hdescent : baseEnd_56563 < baseStart_56563 := by decide
  rcases family_descends (prefixWord ++ tailWord_56563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56593 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_56593 : Nat := 118140960795 + 56593 * 2 ^ 59
def prefixEnd_56593 : Nat := 4983230072969 + 3 ^ 40 * 56593 * 2
def baseEnd_56593 : Nat := 19372940453334875551493

theorem tailTrace_56593 : CollatzResearch.WordTrace tailWord_56593 prefixEnd_56593 19372940453334875551493 := by
  unfold tailWord_56593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064116283980701160014433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1376077522653800773342955 2064116283980701160014433)
  ·
    refine ⟨1548087212985525870010825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2064116283980701160014433 1548087212985525870010825)
    ·
      refine ⟨1161065409739144402508119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548087212985525870010825 1161065409739144402508119)
      ·
        refine ⟨1741598114608716603762179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161065409739144402508119 1741598114608716603762179)
        ·
          refine ⟨2612397171913074905643269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741598114608716603762179 2612397171913074905643269)
          ·
            refine ⟨489824469733701544808113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2612397171913074905643269 489824469733701544808113)
            ·
              refine ⟨367368352300276158606085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489824469733701544808113 367368352300276158606085)
              ·
                refine ⟨68881566056301779738641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367368352300276158606085 68881566056301779738641)
                ·
                  refine ⟨51661174542226334803981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68881566056301779738641 51661174542226334803981)
                  ·
                    refine ⟨19372940453334875551493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51661174542226334803981 19372940453334875551493)
                    ·
                      rfl

theorem cell22_56593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_56593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56593 prefixEnd_56593 := by exact prefixLift 56593
  have htrace : WordTrace (prefixWord ++ tailWord_56593) baseStart_56593 baseEnd_56593 := by
    simpa [prefixWord, tailWord_56593, baseEnd_56593] using wordTrace_append hprefix tailTrace_56593
  have hstable : (prefixWord ++ tailWord_56593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56593).length < 2 ^ (prefixWord ++ tailWord_56593).sum := by decide
  have hdescent : baseEnd_56593 < baseStart_56593 := by decide
  rcases family_descends (prefixWord ++ tailWord_56593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56666 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_56666 : Nat := 118140960795 + 56666 * 2 ^ 59
def prefixEnd_56666 : Nat := 4983230072969 + 3 ^ 40 * 56666 * 2
def baseEnd_56666 : Nat := 19397929845187018476269

theorem tailTrace_56666 : CollatzResearch.WordTrace tailWord_56666 prefixEnd_56666 19397929845187018476269 := by
  unfold tailWord_56666
  simp only [CollatzResearch.WordTrace]
  refine ⟨516694703179058656855463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1377852541810823084947901 516694703179058656855463)
  ·
    refine ⟨775042054768587985283195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516694703179058656855463 775042054768587985283195)
    ·
      refine ⟨1162563082152881977924793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775042054768587985283195 1162563082152881977924793)
      ·
        refine ⟨871922311614661483443595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162563082152881977924793 871922311614661483443595)
        ·
          refine ⟨1307883467421992225165393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871922311614661483443595 1307883467421992225165393)
          ·
            refine ⟨980912600566494168874045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307883467421992225165393 980912600566494168874045)
            ·
              refine ⟨367842225212435313327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 980912600566494168874045 367842225212435313327767)
              ·
                refine ⟨551763337818652969991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367842225212435313327767 551763337818652969991651)
                ·
                  refine ⟨827645006727979454987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551763337818652969991651 827645006727979454987477)
                  ·
                    refine ⟨19397929845187018476269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 827645006727979454987477 19397929845187018476269)
                    ·
                      rfl

theorem cell22_56666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_56666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56666 prefixEnd_56666 := by exact prefixLift 56666
  have htrace : WordTrace (prefixWord ++ tailWord_56666) baseStart_56666 baseEnd_56666 := by
    simpa [prefixWord, tailWord_56666, baseEnd_56666] using wordTrace_append hprefix tailTrace_56666
  have hstable : (prefixWord ++ tailWord_56666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56666).length < 2 ^ (prefixWord ++ tailWord_56666).sum := by decide
  have hdescent : baseEnd_56666 < baseStart_56666 := by decide
  rcases family_descends (prefixWord ++ tailWord_56666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56698 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_56698 : Nat := 118140960795 + 56698 * 2 ^ 59
def prefixEnd_56698 : Nat := 4983230072969 + 3 ^ 40 * 56698 * 2
def baseEnd_56698 : Nat := 19408884099149601676171

theorem tailTrace_56698 : CollatzResearch.WordTrace tailWord_56698 prefixEnd_56698 19408884099149601676171 := by
  unfold tailWord_56698
  simp only [CollatzResearch.WordTrace]
  refine ⟨516986487150076023146687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1378630632400202728391165 516986487150076023146687)
  ·
    refine ⟨775479730725114034720031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516986487150076023146687 775479730725114034720031)
    ·
      refine ⟨1163219596087671052080047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775479730725114034720031 1163219596087671052080047)
      ·
        refine ⟨1744829394131506578120071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163219596087671052080047 1744829394131506578120071)
        ·
          refine ⟨2617244091197259867180107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744829394131506578120071 2617244091197259867180107)
          ·
            refine ⟨3925866136795889800770161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617244091197259867180107 3925866136795889800770161)
            ·
              refine ⟨2944399602596917350577621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925866136795889800770161 2944399602596917350577621)
              ·
                refine ⟨69009365685865250404163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2944399602596917350577621 69009365685865250404163)
                ·
                  refine ⟨103514048528797875606245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69009365685865250404163 103514048528797875606245)
                  ·
                    refine ⟨19408884099149601676171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103514048528797875606245 19408884099149601676171)
                    ·
                      rfl

theorem cell22_56698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_56698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56698 prefixEnd_56698 := by exact prefixLift 56698
  have htrace : WordTrace (prefixWord ++ tailWord_56698) baseStart_56698 baseEnd_56698 := by
    simpa [prefixWord, tailWord_56698, baseEnd_56698] using wordTrace_append hprefix tailTrace_56698
  have hstable : (prefixWord ++ tailWord_56698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56698).length < 2 ^ (prefixWord ++ tailWord_56698).sum := by decide
  have hdescent : baseEnd_56698 < baseStart_56698 := by decide
  rcases family_descends (prefixWord ++ tailWord_56698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56702 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_56702 : Nat := 118140960795 + 56702 * 2 ^ 59
def prefixEnd_56702 : Nat := 4983230072969 + 3 ^ 40 * 56702 * 2
def baseEnd_56702 : Nat := 6470084460298308192053

theorem tailTrace_56702 : CollatzResearch.WordTrace tailWord_56702 prefixEnd_56702 6470084460298308192053 := by
  unfold tailWord_56702
  simp only [CollatzResearch.WordTrace]
  refine ⟨258511480073226596966545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1378727893723875183821573 258511480073226596966545)
  ·
    refine ⟨193883610054919947724909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258511480073226596966545 193883610054919947724909)
    ·
      refine ⟨72706353770594980396841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193883610054919947724909 72706353770594980396841)
      ·
        refine ⟨54529765327946235297631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72706353770594980396841 54529765327946235297631)
        ·
          refine ⟨81794647991919352946447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54529765327946235297631 81794647991919352946447)
          ·
            refine ⟨122691971987879029419671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81794647991919352946447 122691971987879029419671)
            ·
              refine ⟨184037957981818544129507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122691971987879029419671 184037957981818544129507)
              ·
                refine ⟨276056936972727816194261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184037957981818544129507 276056936972727816194261)
                ·
                  refine ⟨6470084460298308192053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276056936972727816194261 6470084460298308192053)
                  ·
                    rfl

theorem cell22_56702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_56702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56702 prefixEnd_56702 := by exact prefixLift 56702
  have htrace : WordTrace (prefixWord ++ tailWord_56702) baseStart_56702 baseEnd_56702 := by
    simpa [prefixWord, tailWord_56702, baseEnd_56702] using wordTrace_append hprefix tailTrace_56702
  have hstable : (prefixWord ++ tailWord_56702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56702).length < 2 ^ (prefixWord ++ tailWord_56702).sum := by decide
  have hdescent : baseEnd_56702 < baseStart_56702 := by decide
  rcases family_descends (prefixWord ++ tailWord_56702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56743 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_56743 : Nat := 118140960795 + 56743 * 2 ^ 59
def prefixEnd_56743 : Nat := 4983230072969 + 3 ^ 40 * 56743 * 2
def baseEnd_56743 : Nat := 19424288518784484301033

theorem tailTrace_56743 : CollatzResearch.WordTrace tailWord_56743 prefixEnd_56743 19424288518784484301033 := by
  unfold tailWord_56743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069587233437276777974883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1379724822291517851983255 2069587233437276777974883)
  ·
    refine ⟨3104380850155915166962325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069587233437276777974883 3104380850155915166962325)
    ·
      refine ⟨145517852351058523451359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3104380850155915166962325 145517852351058523451359)
      ·
        refine ⟨218276778526587785177039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145517852351058523451359 218276778526587785177039)
        ·
          refine ⟨327415167789881677765559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218276778526587785177039 327415167789881677765559)
          ·
            refine ⟨491122751684822516648339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327415167789881677765559 491122751684822516648339)
            ·
              refine ⟨736684127527233774972509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491122751684822516648339 736684127527233774972509)
              ·
                refine ⟨276256547822712665614691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 736684127527233774972509 276256547822712665614691)
                ·
                  refine ⟨414384821734068998422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 276256547822712665614691 414384821734068998422037)
                  ·
                    refine ⟨19424288518784484301033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 414384821734068998422037 19424288518784484301033)
                    ·
                      rfl

theorem cell22_56743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_56743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56743 prefixEnd_56743 := by exact prefixLift 56743
  have htrace : WordTrace (prefixWord ++ tailWord_56743) baseStart_56743 baseEnd_56743 := by
    simpa [prefixWord, tailWord_56743, baseEnd_56743] using wordTrace_append hprefix tailTrace_56743
  have hstable : (prefixWord ++ tailWord_56743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56743).length < 2 ^ (prefixWord ++ tailWord_56743).sum := by decide
  have hdescent : baseEnd_56743 < baseStart_56743 := by decide
  rcases family_descends (prefixWord ++ tailWord_56743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56764 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_56764 : Nat := 118140960795 + 56764 * 2 ^ 59
def prefixEnd_56764 : Nat := 4983230072969 + 3 ^ 40 * 56764 * 2
def baseEnd_56764 : Nat := 6477159082649143175323

theorem tailTrace_56764 : CollatzResearch.WordTrace tailWord_56764 prefixEnd_56764 6477159082649143175323 := by
  unfold tailWord_56764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035176583180598682244673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1380235444240798242992897 1035176583180598682244673)
  ·
    refine ⟨776382437385449011683505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1035176583180598682244673 776382437385449011683505)
    ·
      refine ⟨582286828039086758762629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776382437385449011683505 582286828039086758762629)
      ·
        refine ⟨109178780257328767267993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582286828039086758762629 109178780257328767267993)
        ·
          refine ⟨81884085192996575450995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109178780257328767267993 81884085192996575450995)
          ·
            refine ⟨122826127789494863176493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81884085192996575450995 122826127789494863176493)
            ·
              refine ⟨46059797921060573691185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122826127789494863176493 46059797921060573691185)
              ·
                refine ⟨34544848440795430268389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46059797921060573691185 34544848440795430268389)
                ·
                  refine ⟨6477159082649143175323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34544848440795430268389 6477159082649143175323)
                  ·
                    rfl

theorem cell22_56764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_56764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56764 prefixEnd_56764 := by exact prefixLift 56764
  have htrace : WordTrace (prefixWord ++ tailWord_56764) baseStart_56764 baseEnd_56764 := by
    simpa [prefixWord, tailWord_56764, baseEnd_56764] using wordTrace_append hprefix tailTrace_56764
  have hstable : (prefixWord ++ tailWord_56764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56764).length < 2 ^ (prefixWord ++ tailWord_56764).sum := by decide
  have hdescent : baseEnd_56764 < baseStart_56764 := by decide
  rcases family_descends (prefixWord ++ tailWord_56764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56770 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_56770 : Nat := 118140960795 + 56770 * 2 ^ 59
def prefixEnd_56770 : Nat := 4983230072969 + 3 ^ 40 * 56770 * 2
def baseEnd_56770 : Nat := 6477843723521804625317

theorem tailTrace_56770 : CollatzResearch.WordTrace tailWord_56770 prefixEnd_56770 6477843723521804625317 := by
  unfold tailWord_56770
  simp only [CollatzResearch.WordTrace]
  refine ⟨517643001084865097301941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1380381336226306926138509 517643001084865097301941)
  ·
    refine ⟨48529031351706102872057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 517643001084865097301941 48529031351706102872057)
    ·
      refine ⟨36396773513779577154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48529031351706102872057 36396773513779577154043)
      ·
        refine ⟨54595160270669365731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36396773513779577154043 54595160270669365731065)
        ·
          refine ⟨40946370203002024298299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54595160270669365731065 40946370203002024298299)
          ·
            refine ⟨61419555304503036447449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40946370203002024298299 61419555304503036447449)
            ·
              refine ⟨46064666478377277335587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61419555304503036447449 46064666478377277335587)
              ·
                refine ⟨69096999717565916003381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46064666478377277335587 69096999717565916003381)
                ·
                  refine ⟨6477843723521804625317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69096999717565916003381 6477843723521804625317)
                  ·
                    rfl

theorem cell22_56770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_56770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56770 prefixEnd_56770 := by exact prefixLift 56770
  have htrace : WordTrace (prefixWord ++ tailWord_56770) baseStart_56770 baseEnd_56770 := by
    simpa [prefixWord, tailWord_56770, baseEnd_56770] using wordTrace_append hprefix tailTrace_56770
  have hstable : (prefixWord ++ tailWord_56770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56770).length < 2 ^ (prefixWord ++ tailWord_56770).sum := by decide
  have hdescent : baseEnd_56770 < baseStart_56770 := by decide
  rcases family_descends (prefixWord ++ tailWord_56770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56824 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_56824 : Nat := 118140960795 + 56824 * 2 ^ 59
def prefixEnd_56824 : Nat := 4983230072969 + 3 ^ 40 * 56824 * 2
def baseEnd_56824 : Nat := 19452016474127273025785

theorem tailTrace_56824 : CollatzResearch.WordTrace tailWord_56824 prefixEnd_56824 19452016474127273025785 := by
  unfold tailWord_56824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036270773071913805836763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1381694364095885074449017 1036270773071913805836763)
  ·
    refine ⟨1554406159607870708755145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036270773071913805836763 1554406159607870708755145)
    ·
      refine ⟨1165804619705903031566359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554406159607870708755145 1165804619705903031566359)
      ·
        refine ⟨1748706929558854547349539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165804619705903031566359 1748706929558854547349539)
        ·
          refine ⟨2623060394338281821024309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748706929558854547349539 2623060394338281821024309)
          ·
            refine ⟨245911911969213920721029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2623060394338281821024309 245911911969213920721029)
            ·
              refine ⟨46108483494227610135193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245911911969213920721029 46108483494227610135193)
              ·
                refine ⟨34581362620670707601395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46108483494227610135193 34581362620670707601395)
                ·
                  refine ⟨51872043931006061402093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34581362620670707601395 51872043931006061402093)
                  ·
                    refine ⟨19452016474127273025785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51872043931006061402093 19452016474127273025785)
                    ·
                      rfl

theorem cell22_56824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_56824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56824 prefixEnd_56824 := by exact prefixLift 56824
  have htrace : WordTrace (prefixWord ++ tailWord_56824) baseStart_56824 baseEnd_56824 := by
    simpa [prefixWord, tailWord_56824, baseEnd_56824] using wordTrace_append hprefix tailTrace_56824
  have hstable : (prefixWord ++ tailWord_56824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56824).length < 2 ^ (prefixWord ++ tailWord_56824).sum := by decide
  have hdescent : baseEnd_56824 < baseStart_56824 := by decide
  rcases family_descends (prefixWord ++ tailWord_56824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56867 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 1, 4]
def baseStart_56867 : Nat := 118140960795 + 56867 * 2 ^ 59
def prefixEnd_56867 : Nat := 4983230072969 + 3 ^ 40 * 56867 * 2
def baseEnd_56867 : Nat := 19466736252889494200653

theorem tailTrace_56867 : CollatzResearch.WordTrace tailWord_56867 prefixEnd_56867 19466736252889494200653 := by
  unfold tailWord_56867
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074109884988045955488855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382739923325363970325903 2074109884988045955488855)
  ·
    refine ⟨3111164827482068933233283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074109884988045955488855 3111164827482068933233283)
    ·
      refine ⟨4666747241223103399849925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111164827482068933233283 4666747241223103399849925)
      ·
        refine ⟨875015107729331887471861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4666747241223103399849925 875015107729331887471861)
        ·
          refine ⟨82032666349624864450487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 875015107729331887471861 82032666349624864450487)
          ·
            refine ⟨123048999524437296675731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82032666349624864450487 123048999524437296675731)
            ·
              refine ⟨184573499286655945013597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123048999524437296675731 184573499286655945013597)
              ·
                refine ⟨69215062232495979380099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184573499286655945013597 69215062232495979380099)
                ·
                  refine ⟨103822593348743969070149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69215062232495979380099 103822593348743969070149)
                  ·
                    refine ⟨19466736252889494200653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103822593348743969070149 19466736252889494200653)
                    ·
                      rfl

theorem cell22_56867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_56867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56867 prefixEnd_56867 := by exact prefixLift 56867
  have htrace : WordTrace (prefixWord ++ tailWord_56867) baseStart_56867 baseEnd_56867 := by
    simpa [prefixWord, tailWord_56867, baseEnd_56867] using wordTrace_append hprefix tailTrace_56867
  have hstable : (prefixWord ++ tailWord_56867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56867).length < 2 ^ (prefixWord ++ tailWord_56867).sum := by decide
  have hdescent : baseEnd_56867 < baseStart_56867 := by decide
  rcases family_descends (prefixWord ++ tailWord_56867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56955 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 5]
def baseStart_56955 : Nat := 118140960795 + 56955 * 2 ^ 59
def prefixEnd_56955 : Nat := 4983230072969 + 3 ^ 40 * 56955 * 2
def baseEnd_56955 : Nat := 6498953483762199333461

theorem tailTrace_56955 : CollatzResearch.WordTrace tailWord_56955 prefixEnd_56955 6498953483762199333461 := by
  unfold tailWord_56955
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077319508669236984692319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1384879672446157989794879 2077319508669236984692319)
  ·
    refine ⟨3115979263003855477038479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2077319508669236984692319 3115979263003855477038479)
    ·
      refine ⟨4673968894505783215557719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115979263003855477038479 4673968894505783215557719)
      ·
        refine ⟨7010953341758674823336579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673968894505783215557719 7010953341758674823336579)
        ·
          refine ⟨10516430012638012235004869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010953341758674823336579 10516430012638012235004869)
          ·
            refine ⟨1971830627369627294063413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10516430012638012235004869 1971830627369627294063413)
            ·
              refine ⟨184859121315902558818445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1971830627369627294063413 184859121315902558818445)
              ·
                refine ⟨69322170493463459556917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184859121315902558818445 69322170493463459556917)
                ·
                  refine ⟨6498953483762199333461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69322170493463459556917 6498953483762199333461)
                  ·
                    rfl

theorem cell22_56955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].length) (baseStart_56955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56955 prefixEnd_56955 := by exact prefixLift 56955
  have htrace : WordTrace (prefixWord ++ tailWord_56955) baseStart_56955 baseEnd_56955 := by
    simpa [prefixWord, tailWord_56955, baseEnd_56955] using wordTrace_append hprefix tailTrace_56955
  have hstable : (prefixWord ++ tailWord_56955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56955).length < 2 ^ (prefixWord ++ tailWord_56955).sum := by decide
  have hdescent : baseEnd_56955 < baseStart_56955 := by decide
  rcases family_descends (prefixWord ++ tailWord_56955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56993 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_56993 : Nat := 118140960795 + 56993 * 2 ^ 59
def prefixEnd_56993 : Nat := 4983230072969 + 3 ^ 40 * 56993 * 2
def baseEnd_56993 : Nat := 19509868627867165550267

theorem tailTrace_56993 : CollatzResearch.WordTrace tailWord_56993 prefixEnd_56993 19509868627867165550267 := by
  unfold tailWord_56993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078705482531569474575633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1385803655021046316383755 2078705482531569474575633)
  ·
    refine ⟨1559029111898677105931725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2078705482531569474575633 1559029111898677105931725)
    ·
      refine ⟨584635916962003914724397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1559029111898677105931725 584635916962003914724397)
      ·
        refine ⟨219238468860751468021649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584635916962003914724397 219238468860751468021649)
        ·
          refine ⟨164428851645563601016237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219238468860751468021649 164428851645563601016237)
          ·
            refine ⟨61660819367086350381089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164428851645563601016237 61660819367086350381089)
            ·
              refine ⟨46245614525314762785817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61660819367086350381089 46245614525314762785817)
              ·
                refine ⟨34684210893986072089363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46245614525314762785817 34684210893986072089363)
                ·
                  refine ⟨52026316340979108134045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34684210893986072089363 52026316340979108134045)
                  ·
                    refine ⟨19509868627867165550267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52026316340979108134045 19509868627867165550267)
                    ·
                      rfl

theorem cell22_56993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_56993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_56993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_56993 prefixEnd_56993 := by exact prefixLift 56993
  have htrace : WordTrace (prefixWord ++ tailWord_56993) baseStart_56993 baseEnd_56993 := by
    simpa [prefixWord, tailWord_56993, baseEnd_56993] using wordTrace_append hprefix tailTrace_56993
  have hstable : (prefixWord ++ tailWord_56993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56993).length < 2 ^ (prefixWord ++ tailWord_56993).sum := by decide
  have hdescent : baseEnd_56993 < baseStart_56993 := by decide
  rcases family_descends (prefixWord ++ tailWord_56993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57032 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_57032 : Nat := 118140960795 + 57032 * 2 ^ 59
def prefixEnd_57032 : Nat := 4983230072969 + 3 ^ 40 * 57032 * 2
def baseEnd_57032 : Nat := 19523219124884063825147

theorem tailTrace_57032 : CollatzResearch.WordTrace tailWord_57032 prefixEnd_57032 19523219124884063825147 := by
  unfold tailWord_57032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040063964695139567622675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1386751952926852756830233 1040063964695139567622675)
  ·
    refine ⟨1560095947042709351434013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1040063964695139567622675 1560095947042709351434013)
    ·
      refine ⟨585035980141016006787755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1560095947042709351434013 585035980141016006787755)
      ·
        refine ⟨877553970211524010181633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585035980141016006787755 877553970211524010181633)
        ·
          refine ⟨658165477658643007636225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877553970211524010181633 658165477658643007636225)
          ·
            refine ⟨493624108243982255727169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 658165477658643007636225 493624108243982255727169)
            ·
              refine ⟨370218081182986691795377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493624108243982255727169 370218081182986691795377)
              ·
                refine ⟨277663560887240018846533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370218081182986691795377 277663560887240018846533)
                ·
                  refine ⟨52061917666357503533725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277663560887240018846533 52061917666357503533725)
                  ·
                    refine ⟨19523219124884063825147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52061917666357503533725 19523219124884063825147)
                    ·
                      rfl

theorem cell22_57032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_57032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57032 prefixEnd_57032 := by exact prefixLift 57032
  have htrace : WordTrace (prefixWord ++ tailWord_57032) baseStart_57032 baseEnd_57032 := by
    simpa [prefixWord, tailWord_57032, baseEnd_57032] using wordTrace_append hprefix tailTrace_57032
  have hstable : (prefixWord ++ tailWord_57032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57032).length < 2 ^ (prefixWord ++ tailWord_57032).sum := by decide
  have hdescent : baseEnd_57032 < baseStart_57032 := by decide
  rcases family_descends (prefixWord ++ tailWord_57032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57049 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_57049 : Nat := 118140960795 + 57049 * 2 ^ 59
def prefixEnd_57049 : Nat := 4983230072969 + 3 ^ 40 * 57049 * 2
def baseEnd_57049 : Nat := 19529038572301686150095

theorem tailTrace_57049 : CollatzResearch.WordTrace tailWord_57049 prefixEnd_57049 19529038572301686150095 := by
  unfold tailWord_57049
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080747970328691038614201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1387165313552460692409467 2080747970328691038614201)
  ·
    refine ⟨1560560977746518278960651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2080747970328691038614201 1560560977746518278960651)
    ·
      refine ⟨2340841466619777418440977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560560977746518278960651 2340841466619777418440977)
      ·
        refine ⟨1755631099964833063830733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2340841466619777418440977 1755631099964833063830733)
        ·
          refine ⟨658361662486812398936525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1755631099964833063830733 658361662486812398936525)
          ·
            refine ⟨246885623432554649601197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658361662486812398936525 246885623432554649601197)
            ·
              refine ⟨92582108787207993600449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246885623432554649601197 92582108787207993600449)
              ·
                refine ⟨69436581590405995200337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92582108787207993600449 69436581590405995200337)
                ·
                  refine ⟨52077436192804496400253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69436581590405995200337 52077436192804496400253)
                  ·
                    refine ⟨19529038572301686150095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52077436192804496400253 19529038572301686150095)
                    ·
                      rfl

theorem cell22_57049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_57049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57049 prefixEnd_57049 := by exact prefixLift 57049
  have htrace : WordTrace (prefixWord ++ tailWord_57049) baseStart_57049 baseEnd_57049 := by
    simpa [prefixWord, tailWord_57049, baseEnd_57049] using wordTrace_append hprefix tailTrace_57049
  have hstable : (prefixWord ++ tailWord_57049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57049).length < 2 ^ (prefixWord ++ tailWord_57049).sum := by decide
  have hdescent : baseEnd_57049 < baseStart_57049 := by decide
  rcases family_descends (prefixWord ++ tailWord_57049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57075 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_57075 : Nat := 118140960795 + 57075 * 2 ^ 59
def prefixEnd_57075 : Nat := 4983230072969 + 3 ^ 40 * 57075 * 2
def baseEnd_57075 : Nat := 19537938903646285000015

theorem tailTrace_57075 : CollatzResearch.WordTrace tailWord_57075 prefixEnd_57075 19537938903646285000015 := by
  unfold tailWord_57075
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081696268234497479060679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1387797512156331652707119 2081696268234497479060679)
  ·
    refine ⟨3122544402351746218591019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081696268234497479060679 3122544402351746218591019)
    ·
      refine ⟨4683816603527619327886529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122544402351746218591019 4683816603527619327886529)
      ·
        refine ⟨3512862452645714495914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4683816603527619327886529 3512862452645714495914897)
        ·
          refine ⟨2634646839484285871936173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512862452645714495914897 2634646839484285871936173)
          ·
            refine ⟨987992564806607201976065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2634646839484285871936173 987992564806607201976065)
            ·
              refine ⟨740994423604955401482049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987992564806607201976065 740994423604955401482049)
              ·
                refine ⟨555745817703716551111537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740994423604955401482049 555745817703716551111537)
                ·
                  refine ⟨416809363277787413333653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555745817703716551111537 416809363277787413333653)
                  ·
                    refine ⟨19537938903646285000015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 416809363277787413333653 19537938903646285000015)
                    ·
                      rfl

theorem cell22_57075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_57075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57075 prefixEnd_57075 := by exact prefixLift 57075
  have htrace : WordTrace (prefixWord ++ tailWord_57075) baseStart_57075 baseEnd_57075 := by
    simpa [prefixWord, tailWord_57075, baseEnd_57075] using wordTrace_append hprefix tailTrace_57075
  have hstable : (prefixWord ++ tailWord_57075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57075).length < 2 ^ (prefixWord ++ tailWord_57075).sum := by decide
  have hdescent : baseEnd_57075 < baseStart_57075 := by decide
  rcases family_descends (prefixWord ++ tailWord_57075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57111 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 3, 3]
def baseStart_57111 : Nat := 118140960795 + 57111 * 2 ^ 59
def prefixEnd_57111 : Nat := 4983230072969 + 3 ^ 40 * 57111 * 2
def baseEnd_57111 : Nat := 19550262439354191099905

theorem tailTrace_57111 : CollatzResearch.WordTrace tailWord_57111 prefixEnd_57111 19550262439354191099905 := by
  unfold tailWord_57111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083009296104075627371187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1388672864069383751580791 2083009296104075627371187)
  ·
    refine ⟨3124513944156113441056781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083009296104075627371187 3124513944156113441056781)
    ·
      refine ⟨1171692729058542540396293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3124513944156113441056781 1171692729058542540396293)
      ·
        refine ⟨219692386698476726324305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1171692729058542540396293 219692386698476726324305)
        ·
          refine ⟨164769290023857544743229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219692386698476726324305 164769290023857544743229)
          ·
            refine ⟨61788483758946579278711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164769290023857544743229 61788483758946579278711)
            ·
              refine ⟨92682725638419868918067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61788483758946579278711 92682725638419868918067)
              ·
                refine ⟨139024088457629803377101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92682725638419868918067 139024088457629803377101)
                ·
                  refine ⟨52134033171611176266413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139024088457629803377101 52134033171611176266413)
                  ·
                    refine ⟨19550262439354191099905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52134033171611176266413 19550262439354191099905)
                    ·
                      rfl

theorem cell22_57111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_57111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57111 prefixEnd_57111 := by exact prefixLift 57111
  have htrace : WordTrace (prefixWord ++ tailWord_57111) baseStart_57111 baseEnd_57111 := by
    simpa [prefixWord, tailWord_57111, baseEnd_57111] using wordTrace_append hprefix tailTrace_57111
  have hstable : (prefixWord ++ tailWord_57111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57111).length < 2 ^ (prefixWord ++ tailWord_57111).sum := by decide
  have hdescent : baseEnd_57111 < baseStart_57111 := by decide
  rcases family_descends (prefixWord ++ tailWord_57111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57122 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_57122 : Nat := 118140960795 + 57122 * 2 ^ 59
def prefixEnd_57122 : Nat := 4983230072969 + 3 ^ 40 * 57122 * 2
def baseEnd_57122 : Nat := 19554027964153829074871

theorem tailTrace_57122 : CollatzResearch.WordTrace tailWord_57122 prefixEnd_57122 19554027964153829074871 := by
  unfold tailWord_57122
  simp only [CollatzResearch.WordTrace]
  refine ⟨520852624766056126505405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1388940332709483004014413 520852624766056126505405)
  ·
    refine ⟨195319734287271047439527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 520852624766056126505405 195319734287271047439527)
    ·
      refine ⟨292979601430906571159291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195319734287271047439527 292979601430906571159291)
      ·
        refine ⟨439469402146359856738937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292979601430906571159291 439469402146359856738937)
        ·
          refine ⟨329602051609769892554203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439469402146359856738937 329602051609769892554203)
          ·
            refine ⟨494403077414654838831305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329602051609769892554203 494403077414654838831305)
            ·
              refine ⟨370802308060991129123479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494403077414654838831305 370802308060991129123479)
              ·
                refine ⟨556203462091486693685219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 370802308060991129123479 556203462091486693685219)
                ·
                  refine ⟨834305193137230040527829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556203462091486693685219 834305193137230040527829)
                  ·
                    refine ⟨19554027964153829074871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 834305193137230040527829 19554027964153829074871)
                    ·
                      rfl

theorem cell22_57122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_57122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57122 prefixEnd_57122 := by exact prefixLift 57122
  have htrace : WordTrace (prefixWord ++ tailWord_57122) baseStart_57122 baseEnd_57122 := by
    simpa [prefixWord, tailWord_57122, baseEnd_57122] using wordTrace_append hprefix tailTrace_57122
  have hstable : (prefixWord ++ tailWord_57122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57122).length < 2 ^ (prefixWord ++ tailWord_57122).sum := by decide
  have hdescent : baseEnd_57122 < baseStart_57122 := by decide
  rcases family_descends (prefixWord ++ tailWord_57122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57124 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_57124 : Nat := 118140960795 + 57124 * 2 ^ 59
def prefixEnd_57124 : Nat := 4983230072969 + 3 ^ 40 * 57124 * 2
def baseEnd_57124 : Nat := 6518237535008830174955

theorem tailTrace_57124 : CollatzResearch.WordTrace tailWord_57124 prefixEnd_57124 6518237535008830174955 := by
  unfold tailWord_57124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041741722528489423797213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1388988963371319231729617 1041741722528489423797213)
  ·
    refine ⟨390653145948183533923955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1041741722528489423797213 390653145948183533923955)
    ·
      refine ⟨585979718922275300885933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390653145948183533923955 585979718922275300885933)
      ·
        refine ⟨219742394595853237832225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 585979718922275300885933 219742394595853237832225)
        ·
          refine ⟨164806795946889928374169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219742394595853237832225 164806795946889928374169)
          ·
            refine ⟨123605096960167446280627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164806795946889928374169 123605096960167446280627)
            ·
              refine ⟨185407645440251169420941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123605096960167446280627 185407645440251169420941)
              ·
                refine ⟨69527867040094188532853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185407645440251169420941 69527867040094188532853)
                ·
                  refine ⟨6518237535008830174955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69527867040094188532853 6518237535008830174955)
                  ·
                    rfl

theorem cell22_57124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_57124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57124 prefixEnd_57124 := by exact prefixLift 57124
  have htrace : WordTrace (prefixWord ++ tailWord_57124) baseStart_57124 baseEnd_57124 := by
    simpa [prefixWord, tailWord_57124, baseEnd_57124] using wordTrace_append hprefix tailTrace_57124
  have hstable : (prefixWord ++ tailWord_57124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57124).length < 2 ^ (prefixWord ++ tailWord_57124).sum := by decide
  have hdescent : baseEnd_57124 < baseStart_57124 := by decide
  rcases family_descends (prefixWord ++ tailWord_57124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57158 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_57158 : Nat := 118140960795 + 57158 * 2 ^ 59
def prefixEnd_57158 : Nat := 4983230072969 + 3 ^ 40 * 57158 * 2
def baseEnd_57158 : Nat := 6522117166620578391587

theorem tailTrace_57158 : CollatzResearch.WordTrace tailWord_57158 prefixEnd_57158 6522117166620578391587 := by
  unfold tailWord_57158
  simp only [CollatzResearch.WordTrace]
  refine ⟨65147610216681332947879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1389815684622535102888085 65147610216681332947879)
  ·
    refine ⟨97721415325021999421819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65147610216681332947879 97721415325021999421819)
    ·
      refine ⟨146582122987532999132729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97721415325021999421819 146582122987532999132729)
      ·
        refine ⟨109936592240649749349547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146582122987532999132729 109936592240649749349547)
        ·
          refine ⟨164904888360974624024321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109936592240649749349547 164904888360974624024321)
          ·
            refine ⟨123678666270730968018241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164904888360974624024321 123678666270730968018241)
            ·
              refine ⟨92758999703048226013681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123678666270730968018241 92758999703048226013681)
              ·
                refine ⟨69569249777286169510261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92758999703048226013681 69569249777286169510261)
                ·
                  refine ⟨6522117166620578391587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69569249777286169510261 6522117166620578391587)
                  ·
                    rfl

theorem cell22_57158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_57158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57158 prefixEnd_57158 := by exact prefixLift 57158
  have htrace : WordTrace (prefixWord ++ tailWord_57158) baseStart_57158 baseEnd_57158 := by
    simpa [prefixWord, tailWord_57158, baseEnd_57158] using wordTrace_append hprefix tailTrace_57158
  have hstable : (prefixWord ++ tailWord_57158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57158).length < 2 ^ (prefixWord ++ tailWord_57158).sum := by decide
  have hdescent : baseEnd_57158 < baseStart_57158 := by decide
  rcases family_descends (prefixWord ++ tailWord_57158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57184 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_57184 : Nat := 118140960795 + 57184 * 2 ^ 59
def prefixEnd_57184 : Nat := 4983230072969 + 3 ^ 40 * 57184 * 2
def baseEnd_57184 : Nat := 19575251831206334024681

theorem tailTrace_57184 : CollatzResearch.WordTrace tailWord_57184 prefixEnd_57184 19575251831206334024681 := by
  unfold tailWord_57184
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042835912419804547389303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1390447883226406063185737 1042835912419804547389303)
  ·
    refine ⟨1564253868629706821083955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042835912419804547389303 1564253868629706821083955)
    ·
      refine ⟨2346380802944560231625933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564253868629706821083955 2346380802944560231625933)
      ·
        refine ⟨879892801104210086859725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2346380802944560231625933 879892801104210086859725)
        ·
          refine ⟨329959800414078782572397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879892801104210086859725 329959800414078782572397)
          ·
            refine ⟨123734925155279543464649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329959800414078782572397 123734925155279543464649)
            ·
              refine ⟨92801193866459657598487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123734925155279543464649 92801193866459657598487)
              ·
                refine ⟨139201790799689486397731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92801193866459657598487 139201790799689486397731)
                ·
                  refine ⟨208802686199534229596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139201790799689486397731 208802686199534229596597)
                  ·
                    refine ⟨19575251831206334024681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208802686199534229596597 19575251831206334024681)
                    ·
                      rfl

theorem cell22_57184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_57184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57184 prefixEnd_57184 := by exact prefixLift 57184
  have htrace : WordTrace (prefixWord ++ tailWord_57184) baseStart_57184 baseEnd_57184 := by
    simpa [prefixWord, tailWord_57184, baseEnd_57184] using wordTrace_append hprefix tailTrace_57184
  have hstable : (prefixWord ++ tailWord_57184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57184).length < 2 ^ (prefixWord ++ tailWord_57184).sum := by decide
  have hdescent : baseEnd_57184 < baseStart_57184 := by decide
  rcases family_descends (prefixWord ++ tailWord_57184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57197 : List Nat := [1, 5, 1, 1, 1, 1, 2, 10]
def baseStart_57197 : Nat := 118140960795 + 57197 * 2 ^ 59
def prefixEnd_57197 : Nat := 4983230072969 + 3 ^ 40 * 57197 * 2
def baseEnd_57197 : Nat := 2175522444097625938849

theorem tailTrace_57197 : CollatzResearch.WordTrace tailWord_57197 prefixEnd_57197 2175522444097625938849 := by
  unfold tailWord_57197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086145973792512315001845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1390763982528341543334563 2086145973792512315001845)
  ·
    refine ⟨195576185043048029531423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2086145973792512315001845 195576185043048029531423)
    ·
      refine ⟨293364277564572044297135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195576185043048029531423 293364277564572044297135)
      ·
        refine ⟨440046416346858066445703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293364277564572044297135 440046416346858066445703)
        ·
          refine ⟨660069624520287099668555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440046416346858066445703 660069624520287099668555)
          ·
            refine ⟨990104436780430649502833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660069624520287099668555 990104436780430649502833)
            ·
              refine ⟨742578327585322987127125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990104436780430649502833 742578327585322987127125)
              ·
                refine ⟨2175522444097625938849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 742578327585322987127125 2175522444097625938849)
                ·
                  rfl

theorem cell22_57197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 10].length) (baseStart_57197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57197 prefixEnd_57197 := by exact prefixLift 57197
  have htrace : WordTrace (prefixWord ++ tailWord_57197) baseStart_57197 baseEnd_57197 := by
    simpa [prefixWord, tailWord_57197, baseEnd_57197] using wordTrace_append hprefix tailTrace_57197
  have hstable : (prefixWord ++ tailWord_57197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57197).length < 2 ^ (prefixWord ++ tailWord_57197).sum := by decide
  have hdescent : baseEnd_57197 < baseStart_57197 := by decide
  rcases family_descends (prefixWord ++ tailWord_57197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57257 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_57257 : Nat := 118140960795 + 57257 * 2 ^ 59
def prefixEnd_57257 : Nat := 4983230072969 + 3 ^ 40 * 57257 * 2
def baseEnd_57257 : Nat := 19600241223058476949457

theorem tailTrace_57257 : CollatzResearch.WordTrace tailWord_57257 prefixEnd_57257 19600241223058476949457 := by
  unfold tailWord_57257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088334353575142562186025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1392222902383428374790683 2088334353575142562186025)
  ·
    refine ⟨1566250765181356921639519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2088334353575142562186025 1566250765181356921639519)
    ·
      refine ⟨2349376147772035382459279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1566250765181356921639519 2349376147772035382459279)
      ·
        refine ⟨3524064221658053073688919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349376147772035382459279 3524064221658053073688919)
        ·
          refine ⟨5286096332487079610533379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524064221658053073688919 5286096332487079610533379)
          ·
            refine ⟨7929144498730619415800069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286096332487079610533379 7929144498730619415800069)
            ·
              refine ⟨1486714593511991140462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7929144498730619415800069 1486714593511991140462513)
              ·
                refine ⟨1115035945133993355346885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486714593511991140462513 1115035945133993355346885)
                ·
                  refine ⟨209069239712623754127541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1115035945133993355346885 209069239712623754127541)
                  ·
                    refine ⟨19600241223058476949457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209069239712623754127541 19600241223058476949457)
                    ·
                      rfl

theorem cell22_57257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_57257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57257 prefixEnd_57257 := by exact prefixLift 57257
  have htrace : WordTrace (prefixWord ++ tailWord_57257) baseStart_57257 baseEnd_57257 := by
    simpa [prefixWord, tailWord_57257, baseEnd_57257] using wordTrace_append hprefix tailTrace_57257
  have hstable : (prefixWord ++ tailWord_57257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57257).length < 2 ^ (prefixWord ++ tailWord_57257).sum := by decide
  have hdescent : baseEnd_57257 < baseStart_57257 := by decide
  rcases family_descends (prefixWord ++ tailWord_57257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57306 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_57306 : Nat := 118140960795 + 57306 * 2 ^ 59
def prefixEnd_57306 : Nat := 4983230072969 + 3 ^ 40 * 57306 * 2
def baseEnd_57306 : Nat := 19617014924438682474307

theorem tailTrace_57306 : CollatzResearch.WordTrace tailWord_57306 prefixEnd_57306 19617014924438682474307 := by
  unfold tailWord_57306
  simp only [CollatzResearch.WordTrace]
  refine ⟨522530382599405982679943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1393414353598415953813181 522530382599405982679943)
  ·
    refine ⟨783795573899108974019915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 522530382599405982679943 783795573899108974019915)
    ·
      refine ⟨1175693360848663461029873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783795573899108974019915 1175693360848663461029873)
      ·
        refine ⟨881770020636497595772405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175693360848663461029873 881770020636497595772405)
        ·
          refine ⟨82665939434671649603663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 881770020636497595772405 82665939434671649603663)
          ·
            refine ⟨123998909152007474405495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82665939434671649603663 123998909152007474405495)
            ·
              refine ⟨185998363728011211608243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123998909152007474405495 185998363728011211608243)
              ·
                refine ⟨278997545592016817412365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185998363728011211608243 278997545592016817412365)
                ·
                  refine ⟨104624079597006306529637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278997545592016817412365 104624079597006306529637)
                  ·
                    refine ⟨19617014924438682474307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104624079597006306529637 19617014924438682474307)
                    ·
                      rfl

theorem cell22_57306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_57306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57306 prefixEnd_57306 := by exact prefixLift 57306
  have htrace : WordTrace (prefixWord ++ tailWord_57306) baseStart_57306 baseEnd_57306 := by
    simpa [prefixWord, tailWord_57306, baseEnd_57306] using wordTrace_append hprefix tailTrace_57306
  have hstable : (prefixWord ++ tailWord_57306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57306).length < 2 ^ (prefixWord ++ tailWord_57306).sum := by decide
  have hdescent : baseEnd_57306 < baseStart_57306 := by decide
  rcases family_descends (prefixWord ++ tailWord_57306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57336 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_57336 : Nat := 118140960795 + 57336 * 2 ^ 59
def prefixEnd_57336 : Nat := 4983230072969 + 3 ^ 40 * 57336 * 2
def baseEnd_57336 : Nat := 19627284537528604224215

theorem tailTrace_57336 : CollatzResearch.WordTrace tailWord_57336 prefixEnd_57336 19627284537528604224215 := by
  unfold tailWord_57336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045607860144469527155931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1394143813525959369541241 1045607860144469527155931)
  ·
    refine ⟨1568411790216704290733897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045607860144469527155931 1568411790216704290733897)
    ·
      refine ⟨1176308842662528218050423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568411790216704290733897 1176308842662528218050423)
      ·
        refine ⟨1764463263993792327075635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176308842662528218050423 1764463263993792327075635)
        ·
          refine ⟨2646694895990688490613453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764463263993792327075635 2646694895990688490613453)
          ·
            refine ⟨992510585996508183980045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2646694895990688490613453 992510585996508183980045)
            ·
              refine ⟨372191469748690568992517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992510585996508183980045 372191469748690568992517)
              ·
                refine ⟨69785900577879481686097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372191469748690568992517 69785900577879481686097)
                ·
                  refine ⟨52339425433409611264573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69785900577879481686097 52339425433409611264573)
                  ·
                    refine ⟨19627284537528604224215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52339425433409611264573 19627284537528604224215)
                    ·
                      rfl

theorem cell22_57336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_57336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57336 prefixEnd_57336 := by exact prefixLift 57336
  have htrace : WordTrace (prefixWord ++ tailWord_57336) baseStart_57336 baseEnd_57336 := by
    simpa [prefixWord, tailWord_57336, baseEnd_57336] using wordTrace_append hprefix tailTrace_57336
  have hstable : (prefixWord ++ tailWord_57336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57336).length < 2 ^ (prefixWord ++ tailWord_57336).sum := by decide
  have hdescent : baseEnd_57336 < baseStart_57336 := by decide
  rcases family_descends (prefixWord ++ tailWord_57336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57349 : List Nat := [1, 3, 1, 1, 2, 4, 3, 7]
def baseStart_57349 : Nat := 118140960795 + 57349 * 2 ^ 59
def prefixEnd_57349 : Nat := 4983230072969 + 3 ^ 40 * 57349 * 2
def baseEnd_57349 : Nat := 2181303855911211516575

theorem tailTrace_57349 : CollatzResearch.WordTrace tailWord_57349 prefixEnd_57349 2181303855911211516575 := by
  unfold tailWord_57349
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091689869241842274535101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1394459912827894849690067 2091689869241842274535101)
  ·
    refine ⟨784383700965690852950663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2091689869241842274535101 784383700965690852950663)
    ·
      refine ⟨1176575551448536279425995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784383700965690852950663 1176575551448536279425995)
      ·
        refine ⟨1764863327172804419138993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176575551448536279425995 1764863327172804419138993)
        ·
          refine ⟨1323647495379603314354245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764863327172804419138993 1323647495379603314354245)
          ·
            refine ⟨248183905383675621441421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1323647495379603314354245 248183905383675621441421)
            ·
              refine ⟨93068964518878358040533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248183905383675621441421 93068964518878358040533)
              ·
                refine ⟨2181303855911211516575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 93068964518878358040533 2181303855911211516575)
                ·
                  rfl

theorem cell22_57349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 7].length) (baseStart_57349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57349 prefixEnd_57349 := by exact prefixLift 57349
  have htrace : WordTrace (prefixWord ++ tailWord_57349) baseStart_57349 baseEnd_57349 := by
    simpa [prefixWord, tailWord_57349, baseEnd_57349] using wordTrace_append hprefix tailTrace_57349
  have hstable : (prefixWord ++ tailWord_57349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57349).length < 2 ^ (prefixWord ++ tailWord_57349).sum := by decide
  have hdescent : baseEnd_57349 < baseStart_57349 := by decide
  rcases family_descends (prefixWord ++ tailWord_57349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57456 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_57456 : Nat := 118140960795 + 57456 * 2 ^ 59
def prefixEnd_57456 : Nat := 4983230072969 + 3 ^ 40 * 57456 * 2
def baseEnd_57456 : Nat := 6556120996629430407949

theorem tailTrace_57456 : CollatzResearch.WordTrace tailWord_57456 prefixEnd_57456 6556120996629430407949 := by
  unfold tailWord_57456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047796239927099774340111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1397061653236133032453481 1047796239927099774340111)
  ·
    refine ⟨1571694359890649661510167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047796239927099774340111 1571694359890649661510167)
    ·
      refine ⟨2357541539835974492265251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571694359890649661510167 2357541539835974492265251)
      ·
        refine ⟨3536312309753961738397877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357541539835974492265251 3536312309753961738397877)
        ·
          refine ⟨331529279039433912974801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3536312309753961738397877 331529279039433912974801)
          ·
            refine ⟨248646959279575434731101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331529279039433912974801 248646959279575434731101)
            ·
              refine ⟨93242609729840788024163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248646959279575434731101 93242609729840788024163)
              ·
                refine ⟨139863914594761182036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93242609729840788024163 139863914594761182036245)
                ·
                  refine ⟨6556120996629430407949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139863914594761182036245 6556120996629430407949)
                  ·
                    rfl

theorem cell22_57456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_57456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57456 prefixEnd_57456 := by exact prefixLift 57456
  have htrace : WordTrace (prefixWord ++ tailWord_57456) baseStart_57456 baseEnd_57456 := by
    simpa [prefixWord, tailWord_57456, baseEnd_57456] using wordTrace_append hprefix tailTrace_57456
  have hstable : (prefixWord ++ tailWord_57456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57456).length < 2 ^ (prefixWord ++ tailWord_57456).sum := by decide
  have hdescent : baseEnd_57456 < baseStart_57456 := by decide
  rcases family_descends (prefixWord ++ tailWord_57456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_57499 : Nat := 118140960795 + 57499 * 2 ^ 59
def prefixEnd_57499 : Nat := 4983230072969 + 3 ^ 40 * 57499 * 2
def baseEnd_57499 : Nat := 19683082768650512398715

theorem tailTrace_57499 : CollatzResearch.WordTrace tailWord_57499 prefixEnd_57499 19683082768650512398715 := by
  unfold tailWord_57499
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097160818698417892495551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1398107212465611928330367 2097160818698417892495551)
  ·
    refine ⟨3145741228047626838743327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2097160818698417892495551 3145741228047626838743327)
    ·
      refine ⟨4718611842071440258114991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3145741228047626838743327 4718611842071440258114991)
      ·
        refine ⟨7077917763107160387172487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718611842071440258114991 7077917763107160387172487)
        ·
          refine ⟨10616876644660740580758731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077917763107160387172487 10616876644660740580758731)
          ·
            refine ⟨15925314966991110871138097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616876644660740580758731 15925314966991110871138097)
            ·
              refine ⟨11943986225243333153353573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15925314966991110871138097 11943986225243333153353573)
              ·
                refine ⟨2239497417233124966253795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11943986225243333153353573 2239497417233124966253795)
                ·
                  refine ⟨3359246125849687449380693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239497417233124966253795 3359246125849687449380693)
                  ·
                    refine ⟨19683082768650512398715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3359246125849687449380693 19683082768650512398715)
                    ·
                      rfl

theorem cell22_57499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_57499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57499 prefixEnd_57499 := by exact prefixLift 57499
  have htrace : WordTrace (prefixWord ++ tailWord_57499) baseStart_57499 baseEnd_57499 := by
    simpa [prefixWord, tailWord_57499, baseEnd_57499] using wordTrace_append hprefix tailTrace_57499
  have hstable : (prefixWord ++ tailWord_57499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57499).length < 2 ^ (prefixWord ++ tailWord_57499).sum := by decide
  have hdescent : baseEnd_57499 < baseStart_57499 := by decide
  rcases family_descends (prefixWord ++ tailWord_57499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57503 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_57503 : Nat := 118140960795 + 57503 * 2 ^ 59
def prefixEnd_57503 : Nat := 4983230072969 + 3 ^ 40 * 57503 * 2
def baseEnd_57503 : Nat := 19684452050395835298703

theorem tailTrace_57503 : CollatzResearch.WordTrace tailWord_57503 prefixEnd_57503 19684452050395835298703 := by
  unfold tailWord_57503
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097306710683926575641163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1398204473789284383760775 2097306710683926575641163)
  ·
    refine ⟨3145960066025889863461745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2097306710683926575641163 3145960066025889863461745)
    ·
      refine ⟨2359470049519417397596309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145960066025889863461745 2359470049519417397596309)
      ·
        refine ⟨110600158571222690512327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2359470049519417397596309 110600158571222690512327)
        ·
          refine ⟨165900237856834035768491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110600158571222690512327 165900237856834035768491)
          ·
            refine ⟨248850356785251053652737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165900237856834035768491 248850356785251053652737)
            ·
              refine ⟨186637767588938290239553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248850356785251053652737 186637767588938290239553)
              ·
                refine ⟨139978325691703717679665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186637767588938290239553 139978325691703717679665)
                ·
                  refine ⟨104983744268777788259749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139978325691703717679665 104983744268777788259749)
                  ·
                    refine ⟨19684452050395835298703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104983744268777788259749 19684452050395835298703)
                    ·
                      rfl

theorem cell22_57503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_57503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57503 prefixEnd_57503 := by exact prefixLift 57503
  have htrace : WordTrace (prefixWord ++ tailWord_57503) baseStart_57503 baseEnd_57503 := by
    simpa [prefixWord, tailWord_57503, baseEnd_57503] using wordTrace_append hprefix tailTrace_57503
  have hstable : (prefixWord ++ tailWord_57503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57503).length < 2 ^ (prefixWord ++ tailWord_57503).sum := by decide
  have hdescent : baseEnd_57503 < baseStart_57503 := by decide
  rcases family_descends (prefixWord ++ tailWord_57503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57505 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_57505 : Nat := 118140960795 + 57505 * 2 ^ 59
def prefixEnd_57505 : Nat := 4983230072969 + 3 ^ 40 * 57505 * 2
def baseEnd_57505 : Nat := 19685136691268496748697

theorem tailTrace_57505 : CollatzResearch.WordTrace tailWord_57505 prefixEnd_57505 19685136691268496748697 := by
  unfold tailWord_57505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097379656676680917213969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1398253104451120611475979 2097379656676680917213969)
  ·
    refine ⟨1573034742507510687910477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2097379656676680917213969 1573034742507510687910477)
    ·
      refine ⟨589888028440316507966429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573034742507510687910477 589888028440316507966429)
      ·
        refine ⟨221208010665118690487411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589888028440316507966429 221208010665118690487411)
        ·
          refine ⟨331812015997678035731117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221208010665118690487411 331812015997678035731117)
          ·
            refine ⟨124429505999129263399169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331812015997678035731117 124429505999129263399169)
            ·
              refine ⟨93322129499346947549377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124429505999129263399169 93322129499346947549377)
              ·
                refine ⟨69991597124510210662033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93322129499346947549377 69991597124510210662033)
                ·
                  refine ⟨52493697843382657996525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69991597124510210662033 52493697843382657996525)
                  ·
                    refine ⟨19685136691268496748697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52493697843382657996525 19685136691268496748697)
                    ·
                      rfl

theorem cell22_57505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_57505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57505 prefixEnd_57505 := by exact prefixLift 57505
  have htrace : WordTrace (prefixWord ++ tailWord_57505) baseStart_57505 baseEnd_57505 := by
    simpa [prefixWord, tailWord_57505, baseEnd_57505] using wordTrace_append hprefix tailTrace_57505
  have hstable : (prefixWord ++ tailWord_57505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57505).length < 2 ^ (prefixWord ++ tailWord_57505).sum := by decide
  have hdescent : baseEnd_57505 < baseStart_57505 := by decide
  rcases family_descends (prefixWord ++ tailWord_57505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57537 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_57537 : Nat := 118140960795 + 57537 * 2 ^ 59
def prefixEnd_57537 : Nat := 4983230072969 + 3 ^ 40 * 57537 * 2
def baseEnd_57537 : Nat := 19696090945231079948599

theorem tailTrace_57537 : CollatzResearch.WordTrace tailWord_57537 prefixEnd_57537 19696090945231079948599 := by
  unfold tailWord_57537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098546792560750382378865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1399031195040500254919243 2098546792560750382378865)
  ·
    refine ⟨1573910094420562786784149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098546792560750382378865 1573910094420562786784149)
    ·
      refine ⟨73777035675963880630507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1573910094420562786784149 73777035675963880630507)
      ·
        refine ⟨110665553513945820945761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73777035675963880630507 110665553513945820945761)
        ·
          refine ⟨82999165135459365709321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110665553513945820945761 82999165135459365709321)
          ·
            refine ⟨62249373851594524281991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82999165135459365709321 62249373851594524281991)
            ·
              refine ⟨93374060777391786422987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62249373851594524281991 93374060777391786422987)
              ·
                refine ⟨140061091166087679634481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93374060777391786422987 140061091166087679634481)
                ·
                  refine ⟨105045818374565759725861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140061091166087679634481 105045818374565759725861)
                  ·
                    refine ⟨19696090945231079948599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105045818374565759725861 19696090945231079948599)
                    ·
                      rfl

theorem cell22_57537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_57537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57537 prefixEnd_57537 := by exact prefixLift 57537
  have htrace : WordTrace (prefixWord ++ tailWord_57537) baseStart_57537 baseEnd_57537 := by
    simpa [prefixWord, tailWord_57537, baseEnd_57537] using wordTrace_append hprefix tailTrace_57537
  have hstable : (prefixWord ++ tailWord_57537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57537).length < 2 ^ (prefixWord ++ tailWord_57537).sum := by decide
  have hdescent : baseEnd_57537 < baseStart_57537 := by decide
  rcases family_descends (prefixWord ++ tailWord_57537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57546 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_57546 : Nat := 118140960795 + 57546 * 2 ^ 59
def prefixEnd_57546 : Nat := 4983230072969 + 3 ^ 40 * 57546 * 2
def baseEnd_57546 : Nat := 6566390609719352157857

theorem tailTrace_57546 : CollatzResearch.WordTrace tailWord_57546 prefixEnd_57546 6566390609719352157857 := by
  unfold tailWord_57546
  simp only [CollatzResearch.WordTrace]
  refine ⟨524718762382036229864123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1399250033018763279637661 524718762382036229864123)
  ·
    refine ⟨787078143573054344796185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524718762382036229864123 787078143573054344796185)
    ·
      refine ⟨590308607679790758597139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787078143573054344796185 590308607679790758597139)
      ·
        refine ⟨885462911519686137895709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590308607679790758597139 885462911519686137895709)
        ·
          refine ⟨332048591819882301710891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885462911519686137895709 332048591819882301710891)
          ·
            refine ⟨498072887729823452566337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332048591819882301710891 498072887729823452566337)
            ·
              refine ⟨373554665797367589424753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498072887729823452566337 373554665797367589424753)
              ·
                refine ⟨280165999348025692068565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373554665797367589424753 280165999348025692068565)
                ·
                  refine ⟨6566390609719352157857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280165999348025692068565 6566390609719352157857)
                  ·
                    rfl

theorem cell22_57546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_57546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57546 prefixEnd_57546 := by exact prefixLift 57546
  have htrace : WordTrace (prefixWord ++ tailWord_57546) baseStart_57546 baseEnd_57546 := by
    simpa [prefixWord, tailWord_57546, baseEnd_57546] using wordTrace_append hprefix tailTrace_57546
  have hstable : (prefixWord ++ tailWord_57546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57546).length < 2 ^ (prefixWord ++ tailWord_57546).sum := by decide
  have hdescent : baseEnd_57546 < baseStart_57546 := by decide
  rcases family_descends (prefixWord ++ tailWord_57546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57561 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_57561 : Nat := 118140960795 + 57561 * 2 ^ 59
def prefixEnd_57561 : Nat := 4983230072969 + 3 ^ 40 * 57561 * 2
def baseEnd_57561 : Nat := 19704306635703017348525

theorem tailTrace_57561 : CollatzResearch.WordTrace tailWord_57561 prefixEnd_57561 19704306635703017348525 := by
  unfold tailWord_57561
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099422144473802481252537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1399614762982534987501691 2099422144473802481252537)
  ·
    refine ⟨1574566608355351860939403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2099422144473802481252537 1574566608355351860939403)
    ·
      refine ⟨2361849912533027791409105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574566608355351860939403 2361849912533027791409105)
      ·
        refine ⟨1771387434399770843556829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361849912533027791409105 1771387434399770843556829)
        ·
          refine ⟨664270287899914066333811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1771387434399770843556829 664270287899914066333811)
          ·
            refine ⟨996405431849871099500717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664270287899914066333811 996405431849871099500717)
            ·
              refine ⟨373652036943701662312769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996405431849871099500717 373652036943701662312769)
              ·
                refine ⟨280239027707776246734577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373652036943701662312769 280239027707776246734577)
                ·
                  refine ⟨210179270780832185050933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280239027707776246734577 210179270780832185050933)
                  ·
                    refine ⟨19704306635703017348525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210179270780832185050933 19704306635703017348525)
                    ·
                      rfl

theorem cell22_57561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_57561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57561 prefixEnd_57561 := by exact prefixLift 57561
  have htrace : WordTrace (prefixWord ++ tailWord_57561) baseStart_57561 baseEnd_57561 := by
    simpa [prefixWord, tailWord_57561, baseEnd_57561] using wordTrace_append hprefix tailTrace_57561
  have hstable : (prefixWord ++ tailWord_57561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57561).length < 2 ^ (prefixWord ++ tailWord_57561).sum := by decide
  have hdescent : baseEnd_57561 < baseStart_57561 := by decide
  rcases family_descends (prefixWord ++ tailWord_57561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57762 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_57762 : Nat := 118140960795 + 57762 * 2 ^ 59
def prefixEnd_57762 : Nat := 4983230072969 + 3 ^ 40 * 57762 * 2
def baseEnd_57762 : Nat := 19773113043405493072909

theorem tailTrace_57762 : CollatzResearch.WordTrace tailWord_57762 prefixEnd_57762 19773113043405493072909 := by
  unfold tailWord_57762
  simp only [CollatzResearch.WordTrace]
  refine ⟨526688304186403452329885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1404502144497075872879693 526688304186403452329885)
  ·
    refine ⟨197508114069901294623707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 526688304186403452329885 197508114069901294623707)
    ·
      refine ⟨296262171104851941935561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197508114069901294623707 296262171104851941935561)
      ·
        refine ⟨222196628328638956451671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296262171104851941935561 222196628328638956451671)
        ·
          refine ⟨333294942492958434677507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222196628328638956451671 333294942492958434677507)
          ·
            refine ⟨499942413739437652016261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333294942492958434677507 499942413739437652016261)
            ·
              refine ⟨93739202576144559753049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499942413739437652016261 93739202576144559753049)
              ·
                refine ⟨70304401932108419814787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93739202576144559753049 70304401932108419814787)
                ·
                  refine ⟨105456602898162629722181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70304401932108419814787 105456602898162629722181)
                  ·
                    refine ⟨19773113043405493072909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105456602898162629722181 19773113043405493072909)
                    ·
                      rfl

theorem cell22_57762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_57762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57762 prefixEnd_57762 := by exact prefixLift 57762
  have htrace : WordTrace (prefixWord ++ tailWord_57762) baseStart_57762 baseEnd_57762 := by
    simpa [prefixWord, tailWord_57762, baseEnd_57762] using wordTrace_append hprefix tailTrace_57762
  have hstable : (prefixWord ++ tailWord_57762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57762).length < 2 ^ (prefixWord ++ tailWord_57762).sum := by decide
  have hdescent : baseEnd_57762 < baseStart_57762 := by decide
  rcases family_descends (prefixWord ++ tailWord_57762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57770 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_57770 : Nat := 118140960795 + 57770 * 2 ^ 59
def prefixEnd_57770 : Nat := 4983230072969 + 3 ^ 40 * 57770 * 2
def baseEnd_57770 : Nat := 19775851606896138872885

theorem tailTrace_57770 : CollatzResearch.WordTrace tailWord_57770 prefixEnd_57770 19775851606896138872885 := by
  unfold tailWord_57770
  simp only [CollatzResearch.WordTrace]
  refine ⟨526761250179157793902691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1404696667144420783740509 526761250179157793902691)
  ·
    refine ⟨790141875268736690854037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526761250179157793902691 790141875268736690854037)
    ·
      refine ⟨37037900403222032383783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 790141875268736690854037 37037900403222032383783)
      ·
        refine ⟨55556850604833048575675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037900403222032383783 55556850604833048575675)
        ·
          refine ⟨83335275907249572863513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55556850604833048575675 83335275907249572863513)
          ·
            refine ⟨62501456930437179647635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83335275907249572863513 62501456930437179647635)
            ·
              refine ⟨93752185395655769471453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62501456930437179647635 93752185395655769471453)
              ·
                refine ⟨35157069523370913551795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93752185395655769471453 35157069523370913551795)
                ·
                  refine ⟨52735604285056370327693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35157069523370913551795 52735604285056370327693)
                  ·
                    refine ⟨19775851606896138872885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52735604285056370327693 19775851606896138872885)
                    ·
                      rfl

theorem cell22_57770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_57770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57770 prefixEnd_57770 := by exact prefixLift 57770
  have htrace : WordTrace (prefixWord ++ tailWord_57770) baseStart_57770 baseEnd_57770 := by
    simpa [prefixWord, tailWord_57770, baseEnd_57770] using wordTrace_append hprefix tailTrace_57770
  have hstable : (prefixWord ++ tailWord_57770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57770).length < 2 ^ (prefixWord ++ tailWord_57770).sum := by decide
  have hdescent : baseEnd_57770 < baseStart_57770 := by decide
  rcases family_descends (prefixWord ++ tailWord_57770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57777 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 4]
def baseStart_57777 : Nat := 118140960795 + 57777 * 2 ^ 59
def prefixEnd_57777 : Nat := 4983230072969 + 3 ^ 40 * 57777 * 2
def baseEnd_57777 : Nat := 6592749283316817982621

theorem tailTrace_57777 : CollatzResearch.WordTrace tailWord_57777 prefixEnd_57777 6592749283316817982621 := by
  unfold tailWord_57777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2107300311691271371115585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1404866874460847580743723 2107300311691271371115585)
  ·
    refine ⟨1580475233768453528336689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2107300311691271371115585 1580475233768453528336689)
    ·
      refine ⟨1185356425326340146252517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1580475233768453528336689 1185356425326340146252517)
      ·
        refine ⟨222254329748688777422347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1185356425326340146252517 222254329748688777422347)
        ·
          refine ⟨333381494623033166133521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222254329748688777422347 333381494623033166133521)
          ·
            refine ⟨250036120967274874600141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333381494623033166133521 250036120967274874600141)
            ·
              refine ⟨93763545362728077975053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250036120967274874600141 93763545362728077975053)
              ·
                refine ⟨35161329511023029240645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93763545362728077975053 35161329511023029240645)
                ·
                  refine ⟨6592749283316817982621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35161329511023029240645 6592749283316817982621)
                  ·
                    rfl

theorem cell22_57777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_57777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57777 prefixEnd_57777 := by exact prefixLift 57777
  have htrace : WordTrace (prefixWord ++ tailWord_57777) baseStart_57777 baseEnd_57777 := by
    simpa [prefixWord, tailWord_57777, baseEnd_57777] using wordTrace_append hprefix tailTrace_57777
  have hstable : (prefixWord ++ tailWord_57777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57777).length < 2 ^ (prefixWord ++ tailWord_57777).sum := by decide
  have hdescent : baseEnd_57777 < baseStart_57777 := by decide
  rcases family_descends (prefixWord ++ tailWord_57777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57790 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_57790 : Nat := 118140960795 + 57790 * 2 ^ 59
def prefixEnd_57790 : Nat := 4983230072969 + 3 ^ 40 * 57790 * 2
def baseEnd_57790 : Nat := 19782698015622753372823

theorem tailTrace_57790 : CollatzResearch.WordTrace tailWord_57790 prefixEnd_57790 19782698015622753372823 := by
  unfold tailWord_57790
  simp only [CollatzResearch.WordTrace]
  refine ⟨263471807580521823917353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1405182973762783060892549 263471807580521823917353)
  ·
    refine ⟨197603855685391367938015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263471807580521823917353 197603855685391367938015)
    ·
      refine ⟨296405783528087051907023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197603855685391367938015 296405783528087051907023)
      ·
        refine ⟨444608675292130577860535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296405783528087051907023 444608675292130577860535)
        ·
          refine ⟨666913012938195866790803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444608675292130577860535 666913012938195866790803)
          ·
            refine ⟨1000369519407293800186205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666913012938195866790803 1000369519407293800186205)
            ·
              refine ⟨375138569777735175069827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1000369519407293800186205 375138569777735175069827)
              ·
                refine ⟨562707854666602762604741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375138569777735175069827 562707854666602762604741)
                ·
                  refine ⟨105507722749988017988389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562707854666602762604741 105507722749988017988389)
                  ·
                    refine ⟨19782698015622753372823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105507722749988017988389 19782698015622753372823)
                    ·
                      rfl

theorem cell22_57790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_57790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57790 prefixEnd_57790 := by exact prefixLift 57790
  have htrace : WordTrace (prefixWord ++ tailWord_57790) baseStart_57790 baseEnd_57790 := by
    simpa [prefixWord, tailWord_57790, baseEnd_57790] using wordTrace_append hprefix tailTrace_57790
  have hstable : (prefixWord ++ tailWord_57790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57790).length < 2 ^ (prefixWord ++ tailWord_57790).sum := by decide
  have hdescent : baseEnd_57790 < baseStart_57790 := by decide
  rcases family_descends (prefixWord ++ tailWord_57790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57833 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 7]
def baseStart_57833 : Nat := 118140960795 + 57833 * 2 ^ 59
def prefixEnd_57833 : Nat := 4983230072969 + 3 ^ 40 * 57833 * 2
def baseEnd_57833 : Nat := 6599139264794991515897

theorem tailTrace_57833 : CollatzResearch.WordTrace tailWord_57833 prefixEnd_57833 6599139264794991515897 := by
  unfold tailWord_57833
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109342799488392935154153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1406228532992261956769435 2109342799488392935154153)
  ·
    refine ⟨1582007099616294701365615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2109342799488392935154153 1582007099616294701365615)
    ·
      refine ⟨2373010649424442052048423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582007099616294701365615 2373010649424442052048423)
      ·
        refine ⟨3559515974136663078072635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373010649424442052048423 3559515974136663078072635)
        ·
          refine ⟨5339273961204994617108953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559515974136663078072635 5339273961204994617108953)
          ·
            refine ⟨4004455470903745962831715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339273961204994617108953 4004455470903745962831715)
            ·
              refine ⟨6006683206355618944247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004455470903745962831715 6006683206355618944247573)
              ·
                refine ⟨281563275297919638011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6006683206355618944247573 281563275297919638011605)
                ·
                  refine ⟨6599139264794991515897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281563275297919638011605 6599139264794991515897)
                  ·
                    rfl

theorem cell22_57833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_57833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57833 prefixEnd_57833 := by exact prefixLift 57833
  have htrace : WordTrace (prefixWord ++ tailWord_57833) baseStart_57833 baseEnd_57833 := by
    simpa [prefixWord, tailWord_57833, baseEnd_57833] using wordTrace_append hprefix tailTrace_57833
  have hstable : (prefixWord ++ tailWord_57833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57833).length < 2 ^ (prefixWord ++ tailWord_57833).sum := by decide
  have hdescent : baseEnd_57833 < baseStart_57833 := by decide
  rcases family_descends (prefixWord ++ tailWord_57833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57901 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 7]
def baseStart_57901 : Nat := 118140960795 + 57901 * 2 ^ 59
def prefixEnd_57901 : Nat := 4983230072969 + 3 ^ 40 * 57901 * 2
def baseEnd_57901 : Nat := 6606898528018487949161

theorem tailTrace_57901 : CollatzResearch.WordTrace tailWord_57901 prefixEnd_57901 6606898528018487949161 := by
  unfold tailWord_57901
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111822963242040548629557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1407881975494693699086371 2111822963242040548629557)
  ·
    refine ⟨197983402803941301434021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2111822963242040548629557 197983402803941301434021)
    ·
      refine ⟨37121888025738994018879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197983402803941301434021 37121888025738994018879)
      ·
        refine ⟨55682832038608491028319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37121888025738994018879 55682832038608491028319)
        ·
          refine ⟨83524248057912736542479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55682832038608491028319 83524248057912736542479)
          ·
            refine ⟨125286372086869104813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83524248057912736542479 125286372086869104813719)
            ·
              refine ⟨187929558130303657220579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125286372086869104813719 187929558130303657220579)
              ·
                refine ⟨281894337195455485830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187929558130303657220579 281894337195455485830869)
                ·
                  refine ⟨6606898528018487949161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281894337195455485830869 6606898528018487949161)
                  ·
                    rfl

theorem cell22_57901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_57901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57901 prefixEnd_57901 := by exact prefixLift 57901
  have htrace : WordTrace (prefixWord ++ tailWord_57901) baseStart_57901 baseEnd_57901 := by
    simpa [prefixWord, tailWord_57901, baseEnd_57901] using wordTrace_append hprefix tailTrace_57901
  have hstable : (prefixWord ++ tailWord_57901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57901).length < 2 ^ (prefixWord ++ tailWord_57901).sum := by decide
  have hdescent : baseEnd_57901 < baseStart_57901 := by decide
  rcases family_descends (prefixWord ++ tailWord_57901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57912 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_57912 : Nat := 118140960795 + 57912 * 2 ^ 59
def prefixEnd_57912 : Nat := 4983230072969 + 3 ^ 40 * 57912 * 2
def baseEnd_57912 : Nat := 6608153702951700607483

theorem tailTrace_57912 : CollatzResearch.WordTrace tailWord_57912 prefixEnd_57912 6608153702951700607483 := by
  unfold tailWord_57912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056112083101094713639995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1408149444134792951519993 1056112083101094713639995)
  ·
    refine ⟨1584168124651642070459993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056112083101094713639995 1584168124651642070459993)
    ·
      refine ⟨1188126093488731552844995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584168124651642070459993 1188126093488731552844995)
      ·
        refine ⟨1782189140233097329267493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188126093488731552844995 1782189140233097329267493)
        ·
          refine ⟨334160463793705749237655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1782189140233097329267493 334160463793705749237655)
          ·
            refine ⟨501240695690558623856483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334160463793705749237655 501240695690558623856483)
            ·
              refine ⟨751861043535837935784725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501240695690558623856483 751861043535837935784725)
              ·
                refine ⟨35243486415742403239909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751861043535837935784725 35243486415742403239909)
                ·
                  refine ⟨6608153702951700607483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35243486415742403239909 6608153702951700607483)
                  ·
                    rfl

theorem cell22_57912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_57912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57912 prefixEnd_57912 := by exact prefixLift 57912
  have htrace : WordTrace (prefixWord ++ tailWord_57912) baseStart_57912 baseEnd_57912 := by
    simpa [prefixWord, tailWord_57912, baseEnd_57912] using wordTrace_append hprefix tailTrace_57912
  have hstable : (prefixWord ++ tailWord_57912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57912).length < 2 ^ (prefixWord ++ tailWord_57912).sum := by decide
  have hdescent : baseEnd_57912 < baseStart_57912 := by decide
  rcases family_descends (prefixWord ++ tailWord_57912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57925 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_57925 : Nat := 118140960795 + 57925 * 2 ^ 59
def prefixEnd_57925 : Nat := 4983230072969 + 3 ^ 40 * 57925 * 2
def baseEnd_57925 : Nat := 19828911274527401247409

theorem tailTrace_57925 : CollatzResearch.WordTrace tailWord_57925 prefixEnd_57925 19828911274527401247409 := by
  unfold tailWord_57925
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112698315155092647503229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1408465543436728431668819 2112698315155092647503229)
  ·
    refine ⟨792261868183159742813711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2112698315155092647503229 792261868183159742813711)
    ·
      refine ⟨1188392802274739614220567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792261868183159742813711 1188392802274739614220567)
      ·
        refine ⟨1782589203412109421330851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188392802274739614220567 1782589203412109421330851)
        ·
          refine ⟨2673883805118164131996277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782589203412109421330851 2673883805118164131996277)
          ·
            refine ⟨250676606729827887374651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2673883805118164131996277 250676606729827887374651)
            ·
              refine ⟨376014910094741831061977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250676606729827887374651 376014910094741831061977)
              ·
                refine ⟨282011182571056373296483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376014910094741831061977 282011182571056373296483)
                ·
                  refine ⟨423016773856584559944725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282011182571056373296483 423016773856584559944725)
                  ·
                    refine ⟨19828911274527401247409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 423016773856584559944725 19828911274527401247409)
                    ·
                      rfl

theorem cell22_57925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_57925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57925 prefixEnd_57925 := by exact prefixLift 57925
  have htrace : WordTrace (prefixWord ++ tailWord_57925) baseStart_57925 baseEnd_57925 := by
    simpa [prefixWord, tailWord_57925, baseEnd_57925] using wordTrace_append hprefix tailTrace_57925
  have hstable : (prefixWord ++ tailWord_57925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57925).length < 2 ^ (prefixWord ++ tailWord_57925).sum := by decide
  have hdescent : baseEnd_57925 < baseStart_57925 := by decide
  rcases family_descends (prefixWord ++ tailWord_57925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57927 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_57927 : Nat := 118140960795 + 57927 * 2 ^ 59
def prefixEnd_57927 : Nat := 4983230072969 + 3 ^ 40 * 57927 * 2
def baseEnd_57927 : Nat := 19829595915400062697403

theorem tailTrace_57927 : CollatzResearch.WordTrace tailWord_57927 prefixEnd_57927 19829595915400062697403 := by
  unfold tailWord_57927
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112771261147846989076035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1408514174098564659384023 2112771261147846989076035)
  ·
    refine ⟨3169156891721770483614053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112771261147846989076035 3169156891721770483614053)
    ·
      refine ⟨594216917197831965677635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3169156891721770483614053 594216917197831965677635)
      ·
        refine ⟨891325375796747948516453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594216917197831965677635 891325375796747948516453)
        ·
          refine ⟨167123507961890240346835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 891325375796747948516453 167123507961890240346835)
          ·
            refine ⟨250685261942835360520253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167123507961890240346835 250685261942835360520253)
            ·
              refine ⟨94006973228563260195095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250685261942835360520253 94006973228563260195095)
              ·
                refine ⟨141010459842844890292643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94006973228563260195095 141010459842844890292643)
                ·
                  refine ⟨211515689764267335438965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141010459842844890292643 211515689764267335438965)
                  ·
                    refine ⟨19829595915400062697403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 211515689764267335438965 19829595915400062697403)
                    ·
                      rfl

theorem cell22_57927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_57927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57927 prefixEnd_57927 := by exact prefixLift 57927
  have htrace : WordTrace (prefixWord ++ tailWord_57927) baseStart_57927 baseEnd_57927 := by
    simpa [prefixWord, tailWord_57927, baseEnd_57927] using wordTrace_append hprefix tailTrace_57927
  have hstable : (prefixWord ++ tailWord_57927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57927).length < 2 ^ (prefixWord ++ tailWord_57927).sum := by decide
  have hdescent : baseEnd_57927 < baseStart_57927 := by decide
  rcases family_descends (prefixWord ++ tailWord_57927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57957 : List Nat := [1, 3, 1, 3, 4, 2, 8]
def baseStart_57957 : Nat := 118140960795 + 57957 * 2 ^ 59
def prefixEnd_57957 : Nat := 4983230072969 + 3 ^ 40 * 57957 * 2
def baseEnd_57957 : Nat := 734809834388517942493

theorem tailTrace_57957 : CollatzResearch.WordTrace tailWord_57957 prefixEnd_57957 734809834388517942493 := by
  unfold tailWord_57957
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113865451039162112668125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1409243634026108075112083 2113865451039162112668125)
  ·
    refine ⟨792699544139685792250547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2113865451039162112668125 792699544139685792250547)
    ·
      refine ⟨1189049316209528688375821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792699544139685792250547 1189049316209528688375821)
      ·
        refine ⟨445893493578573258140933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1189049316209528688375821 445893493578573258140933)
        ·
          refine ⟨83605030045982485901425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445893493578573258140933 83605030045982485901425)
          ·
            refine ⟨62703772534486864426069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83605030045982485901425 62703772534486864426069)
            ·
              refine ⟨734809834388517942493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 62703772534486864426069 734809834388517942493)
              ·
                rfl

theorem cell22_57957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 8].length) (baseStart_57957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57957 prefixEnd_57957 := by exact prefixLift 57957
  have htrace : WordTrace (prefixWord ++ tailWord_57957) baseStart_57957 baseEnd_57957 := by
    simpa [prefixWord, tailWord_57957, baseEnd_57957] using wordTrace_append hprefix tailTrace_57957
  have hstable : (prefixWord ++ tailWord_57957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57957).length < 2 ^ (prefixWord ++ tailWord_57957).sum := by decide
  have hdescent : baseEnd_57957 < baseStart_57957 := by decide
  rcases family_descends (prefixWord ++ tailWord_57957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57974 : List Nat := [5, 1, 1, 2, 3, 1, 2, 7]
def baseStart_57974 : Nat := 118140960795 + 57974 * 2 ^ 59
def prefixEnd_57974 : Nat := 4983230072969 + 3 ^ 40 * 57974 * 2
def baseEnd_57974 : Nat := 2205076108434178530251

theorem tailTrace_57974 : CollatzResearch.WordTrace tailWord_57974 prefixEnd_57974 2205076108434178530251 := by
  unfold tailWord_57974
  simp only [CollatzResearch.WordTrace]
  refine ⟨132155343248598376002311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1409656994651716010691317 132155343248598376002311)
  ·
    refine ⟨198233014872897564003467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132155343248598376002311 198233014872897564003467)
    ·
      refine ⟨297349522309346346005201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198233014872897564003467 297349522309346346005201)
      ·
        refine ⟨223012141732009759503901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297349522309346346005201 223012141732009759503901)
        ·
          refine ⟨83629553149503659813963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223012141732009759503901 83629553149503659813963)
          ·
            refine ⟨125444329724255489720945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83629553149503659813963 125444329724255489720945)
            ·
              refine ⟨94083247293191617290709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125444329724255489720945 94083247293191617290709)
              ·
                refine ⟨2205076108434178530251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94083247293191617290709 2205076108434178530251)
                ·
                  rfl

theorem cell22_57974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_57974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_57974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_57974 prefixEnd_57974 := by exact prefixLift 57974
  have htrace : WordTrace (prefixWord ++ tailWord_57974) baseStart_57974 baseEnd_57974 := by
    simpa [prefixWord, tailWord_57974, baseEnd_57974] using wordTrace_append hprefix tailTrace_57974
  have hstable : (prefixWord ++ tailWord_57974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57974).length < 2 ^ (prefixWord ++ tailWord_57974).sum := by decide
  have hdescent : baseEnd_57974 < baseStart_57974 := by decide
  rcases family_descends (prefixWord ++ tailWord_57974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58000 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_58000 : Nat := 118140960795 + 58000 * 2 ^ 59
def prefixEnd_58000 : Nat := 4983230072969 + 3 ^ 40 * 58000 * 2
def baseEnd_58000 : Nat := 19854585307252205622179

theorem tailTrace_58000 : CollatzResearch.WordTrace tailWord_58000 prefixEnd_58000 19854585307252205622179 := by
  unfold tailWord_58000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057716894941690228241727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1410289193255586970988969 1057716894941690228241727)
  ·
    refine ⟨1586575342412535342362591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057716894941690228241727 1586575342412535342362591)
    ·
      refine ⟨2379863013618803013543887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586575342412535342362591 2379863013618803013543887)
      ·
        refine ⟨3569794520428204520315831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379863013618803013543887 3569794520428204520315831)
        ·
          refine ⟨5354691780642306780473747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569794520428204520315831 5354691780642306780473747)
          ·
            refine ⟨8032037670963460170710621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354691780642306780473747 8032037670963460170710621)
            ·
              refine ⟨3012014126611297564016483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8032037670963460170710621 3012014126611297564016483)
              ·
                refine ⟨4518021189916946346024725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012014126611297564016483 4518021189916946346024725)
                ·
                  refine ⟨211782243277356859969909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518021189916946346024725 211782243277356859969909)
                  ·
                    refine ⟨19854585307252205622179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 211782243277356859969909 19854585307252205622179)
                    ·
                      rfl

theorem cell22_58000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_58000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58000 prefixEnd_58000 := by exact prefixLift 58000
  have htrace : WordTrace (prefixWord ++ tailWord_58000) baseStart_58000 baseEnd_58000 := by
    simpa [prefixWord, tailWord_58000, baseEnd_58000] using wordTrace_append hprefix tailTrace_58000
  have hstable : (prefixWord ++ tailWord_58000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58000).length < 2 ^ (prefixWord ++ tailWord_58000).sum := by decide
  have hdescent : baseEnd_58000 < baseStart_58000 := by decide
  rcases family_descends (prefixWord ++ tailWord_58000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58047 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 6]
def baseStart_58047 : Nat := 118140960795 + 58047 * 2 ^ 59
def prefixEnd_58047 : Nat := 4983230072969 + 3 ^ 40 * 58047 * 2
def baseEnd_58047 : Nat := 6623558122586583232345

theorem tailTrace_58047 : CollatzResearch.WordTrace tailWord_58047 prefixEnd_58047 6623558122586583232345 := by
  unfold tailWord_58047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117148020713107483444395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1411432013808738322296263 2117148020713107483444395)
  ·
    refine ⟨3175722031069661225166593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2117148020713107483444395 3175722031069661225166593)
    ·
      refine ⟨2381791523302245918874945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175722031069661225166593 2381791523302245918874945)
      ·
        refine ⟨1786343642476684439156209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381791523302245918874945 1786343642476684439156209)
        ·
          refine ⟨1339757731857513329367157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786343642476684439156209 1339757731857513329367157)
          ·
            refine ⟨125602287361641874628171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1339757731857513329367157 125602287361641874628171)
            ·
              refine ⟨188403431042462811942257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125602287361641874628171 188403431042462811942257)
              ·
                refine ⟨141302573281847108956693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188403431042462811942257 141302573281847108956693)
                ·
                  refine ⟨6623558122586583232345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141302573281847108956693 6623558122586583232345)
                  ·
                    rfl

theorem cell22_58047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_58047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58047 prefixEnd_58047 := by exact prefixLift 58047
  have htrace : WordTrace (prefixWord ++ tailWord_58047) baseStart_58047 baseEnd_58047 := by
    simpa [prefixWord, tailWord_58047, baseEnd_58047] using wordTrace_append hprefix tailTrace_58047
  have hstable : (prefixWord ++ tailWord_58047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58047).length < 2 ^ (prefixWord ++ tailWord_58047).sum := by decide
  have hdescent : baseEnd_58047 < baseStart_58047 := by decide
  rcases family_descends (prefixWord ++ tailWord_58047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58066 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_58066 : Nat := 118140960795 + 58066 * 2 ^ 59
def prefixEnd_58066 : Nat := 4983230072969 + 3 ^ 40 * 58066 * 2
def baseEnd_58066 : Nat := 19877178456050033471977

theorem tailTrace_58066 : CollatzResearch.WordTrace tailWord_58066 prefixEnd_58066 19877178456050033471977 := by
  unfold tailWord_58066
  simp only [CollatzResearch.WordTrace]
  refine ⟨529460251911068432096513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1411894005096182485590701 529460251911068432096513)
  ·
    refine ⟨397095188933301324072385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 529460251911068432096513 397095188933301324072385)
    ·
      refine ⟨297821391699975993054289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397095188933301324072385 297821391699975993054289)
      ·
        refine ⟨223366043774981994790717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297821391699975993054289 223366043774981994790717)
        ·
          refine ⟨83762266415618248046519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223366043774981994790717 83762266415618248046519)
          ·
            refine ⟨125643399623427372069779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83762266415618248046519 125643399623427372069779)
            ·
              refine ⟨188465099435141058104669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125643399623427372069779 188465099435141058104669)
              ·
                refine ⟨70674412288177896789251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188465099435141058104669 70674412288177896789251)
                ·
                  refine ⟨106011618432266845183877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70674412288177896789251 106011618432266845183877)
                  ·
                    refine ⟨19877178456050033471977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106011618432266845183877 19877178456050033471977)
                    ·
                      rfl

theorem cell22_58066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_58066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58066 prefixEnd_58066 := by exact prefixLift 58066
  have htrace : WordTrace (prefixWord ++ tailWord_58066) baseStart_58066 baseEnd_58066 := by
    simpa [prefixWord, tailWord_58066, baseEnd_58066] using wordTrace_append hprefix tailTrace_58066
  have hstable : (prefixWord ++ tailWord_58066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58066).length < 2 ^ (prefixWord ++ tailWord_58066).sum := by decide
  have hdescent : baseEnd_58066 < baseStart_58066 := by decide
  rcases family_descends (prefixWord ++ tailWord_58066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58079 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 4, 3]
def baseStart_58079 : Nat := 118140960795 + 58079 * 2 ^ 59
def prefixEnd_58079 : Nat := 4983230072969 + 3 ^ 40 * 58079 * 2
def baseEnd_58079 : Nat := 19881628621722332896937

theorem tailTrace_58079 : CollatzResearch.WordTrace tailWord_58079 prefixEnd_58079 19881628621722332896937 := by
  unfold tailWord_58079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118315156597176948609291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1412210104398117965739527 2118315156597176948609291)
  ·
    refine ⟨3177472734895765422913937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118315156597176948609291 3177472734895765422913937)
    ·
      refine ⟨2383104551171824067185453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177472734895765422913937 2383104551171824067185453)
      ·
        refine ⟨893664206689434025194545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2383104551171824067185453 893664206689434025194545)
        ·
          refine ⟨670248155017075518895909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893664206689434025194545 670248155017075518895909)
          ·
            refine ⟨125671529065701659792983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670248155017075518895909 125671529065701659792983)
            ·
              refine ⟨188507293598552489689475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125671529065701659792983 188507293598552489689475)
              ·
                refine ⟨282760940397828734534213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188507293598552489689475 282760940397828734534213)
                ·
                  refine ⟨53017676324592887725165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282760940397828734534213 53017676324592887725165)
                  ·
                    refine ⟨19881628621722332896937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53017676324592887725165 19881628621722332896937)
                    ·
                      rfl

theorem cell22_58079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_58079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58079 prefixEnd_58079 := by exact prefixLift 58079
  have htrace : WordTrace (prefixWord ++ tailWord_58079) baseStart_58079 baseEnd_58079 := by
    simpa [prefixWord, tailWord_58079, baseEnd_58079] using wordTrace_append hprefix tailTrace_58079
  have hstable : (prefixWord ++ tailWord_58079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58079).length < 2 ^ (prefixWord ++ tailWord_58079).sum := by decide
  have hdescent : baseEnd_58079 < baseStart_58079 := by decide
  rcases family_descends (prefixWord ++ tailWord_58079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58096 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_58096 : Nat := 118140960795 + 58096 * 2 ^ 59
def prefixEnd_58096 : Nat := 4983230072969 + 3 ^ 40 * 58096 * 2
def baseEnd_58096 : Nat := 19887448069139955221885

theorem tailTrace_58096 : CollatzResearch.WordTrace tailWord_58096 prefixEnd_58096 19887448069139955221885 := by
  unfold tailWord_58096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059467598767794425989071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1412623465023725901318761 1059467598767794425989071)
  ·
    refine ⟨1589201398151691638983607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1059467598767794425989071 1589201398151691638983607)
    ·
      refine ⟨2383802097227537458475411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589201398151691638983607 2383802097227537458475411)
      ·
        refine ⟨3575703145841306187713117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383802097227537458475411 3575703145841306187713117)
        ·
          refine ⟨1340888679690489820392419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3575703145841306187713117 1340888679690489820392419)
          ·
            refine ⟨2011333019535734730588629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340888679690489820392419 2011333019535734730588629)
            ·
              refine ⟨47140617645368782748171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2011333019535734730588629 47140617645368782748171)
              ·
                refine ⟨70710926468053174122257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47140617645368782748171 70710926468053174122257)
                ·
                  refine ⟨53033194851039880591693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70710926468053174122257 53033194851039880591693)
                  ·
                    refine ⟨19887448069139955221885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53033194851039880591693 19887448069139955221885)
                    ·
                      rfl

theorem cell22_58096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_58096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58096 prefixEnd_58096 := by exact prefixLift 58096
  have htrace : WordTrace (prefixWord ++ tailWord_58096) baseStart_58096 baseEnd_58096 := by
    simpa [prefixWord, tailWord_58096, baseEnd_58096] using wordTrace_append hprefix tailTrace_58096
  have hstable : (prefixWord ++ tailWord_58096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58096).length < 2 ^ (prefixWord ++ tailWord_58096).sum := by decide
  have hdescent : baseEnd_58096 < baseStart_58096 := by decide
  rcases family_descends (prefixWord ++ tailWord_58096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58100 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_58100 : Nat := 118140960795 + 58100 * 2 ^ 59
def prefixEnd_58100 : Nat := 4983230072969 + 3 ^ 40 * 58100 * 2
def baseEnd_58100 : Nat := 19888817350885278121873

theorem tailTrace_58100 : CollatzResearch.WordTrace tailWord_58100 prefixEnd_58100 19888817350885278121873 := by
  unfold tailWord_58100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059540544760548767561877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1412720726347398356749169 1059540544760548767561877)
  ·
    refine ⟨49665963035650723479463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1059540544760548767561877 49665963035650723479463)
    ·
      refine ⟨74498944553476085219195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49665963035650723479463 74498944553476085219195)
      ·
        refine ⟨111748416830214127828793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74498944553476085219195 111748416830214127828793)
        ·
          refine ⟨83811312622660595871595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111748416830214127828793 83811312622660595871595)
          ·
            refine ⟨125716968933990893807393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83811312622660595871595 125716968933990893807393)
            ·
              refine ⟨94287726700493170355545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125716968933990893807393 94287726700493170355545)
              ·
                refine ⟨70715795025369877766659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94287726700493170355545 70715795025369877766659)
                ·
                  refine ⟨106073692538054816649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70715795025369877766659 106073692538054816649989)
                  ·
                    refine ⟨19888817350885278121873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106073692538054816649989 19888817350885278121873)
                    ·
                      rfl

theorem cell22_58100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_58100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58100 prefixEnd_58100 := by exact prefixLift 58100
  have htrace : WordTrace (prefixWord ++ tailWord_58100) baseStart_58100 baseEnd_58100 := by
    simpa [prefixWord, tailWord_58100, baseEnd_58100] using wordTrace_append hprefix tailTrace_58100
  have hstable : (prefixWord ++ tailWord_58100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58100).length < 2 ^ (prefixWord ++ tailWord_58100).sum := by decide
  have hdescent : baseEnd_58100 < baseStart_58100 := by decide
  rcases family_descends (prefixWord ++ tailWord_58100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58227 : List Nat := [1, 1, 1, 2, 2, 1, 4, 10]
def baseStart_58227 : Nat := 118140960795 + 58227 * 2 ^ 59
def prefixEnd_58227 : Nat := 4983230072969 + 3 ^ 40 * 58227 * 2
def baseEnd_58227 : Nat := 2214699116255475577387

theorem tailTrace_58227 : CollatzResearch.WordTrace tailWord_58227 prefixEnd_58227 2214699116255475577387 := by
  unfold tailWord_58227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123713160060998224996935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1415808773373998816664623 2123713160060998224996935)
  ·
    refine ⟨3185569740091497337495403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2123713160060998224996935 3185569740091497337495403)
    ·
      refine ⟨4778354610137246006243105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185569740091497337495403 4778354610137246006243105)
      ·
        refine ⟨3583765957602934504682329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4778354610137246006243105 3583765957602934504682329)
        ·
          refine ⟨2687824468202200878511747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583765957602934504682329 2687824468202200878511747)
          ·
            refine ⟨4031736702303301317767621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687824468202200878511747 4031736702303301317767621)
            ·
              refine ⟨755950631681868997081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4031736702303301317767621 755950631681868997081429)
              ·
                refine ⟨2214699116255475577387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 755950631681868997081429 2214699116255475577387)
                ·
                  rfl

theorem cell22_58227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_58227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58227 prefixEnd_58227 := by exact prefixLift 58227
  have htrace : WordTrace (prefixWord ++ tailWord_58227) baseStart_58227 baseEnd_58227 := by
    simpa [prefixWord, tailWord_58227, baseEnd_58227] using wordTrace_append hprefix tailTrace_58227
  have hstable : (prefixWord ++ tailWord_58227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58227).length < 2 ^ (prefixWord ++ tailWord_58227).sum := by decide
  have hdescent : baseEnd_58227 < baseStart_58227 := by decide
  rcases family_descends (prefixWord ++ tailWord_58227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58248 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_58248 : Nat := 118140960795 + 58248 * 2 ^ 59
def prefixEnd_58248 : Nat := 4983230072969 + 3 ^ 40 * 58248 * 2
def baseEnd_58248 : Nat := 19939480775462225421419

theorem tailTrace_58248 : CollatzResearch.WordTrace tailWord_58248 prefixEnd_58248 19939480775462225421419 := by
  unfold tailWord_58248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062239546492459405755699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1416319395323279207674265 1062239546492459405755699)
  ·
    refine ⟨1593359319738689108633549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1062239546492459405755699 1593359319738689108633549)
    ·
      refine ⟨597509744902008415737581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1593359319738689108633549 597509744902008415737581)
      ·
        refine ⟨224066154338253155901593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597509744902008415737581 224066154338253155901593)
        ·
          refine ⟨168049615753689866926195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224066154338253155901593 168049615753689866926195)
          ·
            refine ⟨252074423630534800389293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168049615753689866926195 252074423630534800389293)
            ·
              refine ⟨94527908861450550145985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252074423630534800389293 94527908861450550145985)
              ·
                refine ⟨70895931646087912609489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94527908861450550145985 70895931646087912609489)
                ·
                  refine ⟨53171948734565934457117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70895931646087912609489 53171948734565934457117)
                  ·
                    refine ⟨19939480775462225421419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53171948734565934457117 19939480775462225421419)
                    ·
                      rfl

theorem cell22_58248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_58248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58248 prefixEnd_58248 := by exact prefixLift 58248
  have htrace : WordTrace (prefixWord ++ tailWord_58248) baseStart_58248 baseEnd_58248 := by
    simpa [prefixWord, tailWord_58248, baseEnd_58248] using wordTrace_append hprefix tailTrace_58248
  have hstable : (prefixWord ++ tailWord_58248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58248).length < 2 ^ (prefixWord ++ tailWord_58248).sum := by decide
  have hdescent : baseEnd_58248 < baseStart_58248 := by decide
  rcases family_descends (prefixWord ++ tailWord_58248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58276 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_58276 : Nat := 118140960795 + 58276 * 2 ^ 59
def prefixEnd_58276 : Nat := 4983230072969 + 3 ^ 40 * 58276 * 2
def baseEnd_58276 : Nat := 19949065747679485721333

theorem tailTrace_58276 : CollatzResearch.WordTrace tailWord_58276 prefixEnd_58276 19949065747679485721333 := by
  unfold tailWord_58276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062750168441739796765341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1417000224588986395687121 1062750168441739796765341)
  ·
    refine ⟨398531313165652423787003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1062750168441739796765341 398531313165652423787003)
    ·
      refine ⟨597796969748478635680505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398531313165652423787003 597796969748478635680505)
      ·
        refine ⟨448347727311358976760379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597796969748478635680505 448347727311358976760379)
        ·
          refine ⟨672521590967038465140569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448347727311358976760379 672521590967038465140569)
          ·
            refine ⟨504391193225278848855427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672521590967038465140569 504391193225278848855427)
            ·
              refine ⟨756586789837918273283141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504391193225278848855427 756586789837918273283141)
              ·
                refine ⟨141860023094609676240589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756586789837918273283141 141860023094609676240589)
                ·
                  refine ⟨53197508660478628590221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141860023094609676240589 53197508660478628590221)
                  ·
                    refine ⟨19949065747679485721333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53197508660478628590221 19949065747679485721333)
                    ·
                      rfl

theorem cell22_58276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_58276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58276 prefixEnd_58276 := by exact prefixLift 58276
  have htrace : WordTrace (prefixWord ++ tailWord_58276) baseStart_58276 baseEnd_58276 := by
    simpa [prefixWord, tailWord_58276, baseEnd_58276] using wordTrace_append hprefix tailTrace_58276
  have hstable : (prefixWord ++ tailWord_58276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58276).length < 2 ^ (prefixWord ++ tailWord_58276).sum := by decide
  have hdescent : baseEnd_58276 < baseStart_58276 := by decide
  rcases family_descends (prefixWord ++ tailWord_58276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58411 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 5, 3]
def baseStart_58411 : Nat := 118140960795 + 58411 * 2 ^ 59
def prefixEnd_58411 : Nat := 4983230072969 + 3 ^ 40 * 58411 * 2
def baseEnd_58411 : Nat := 19995279006584133595919

theorem tailTrace_58411 : CollatzResearch.WordTrace tailWord_58411 prefixEnd_58411 19995279006584133595919 := by
  unfold tailWord_58411
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130424191394397649695087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1420282794262931766463391 2130424191394397649695087)
  ·
    refine ⟨3195636287091596474542631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130424191394397649695087 3195636287091596474542631)
    ·
      refine ⟨4793454430637394711813947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195636287091596474542631 4793454430637394711813947)
      ·
        refine ⟨7190181645956092067720921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793454430637394711813947 7190181645956092067720921)
        ·
          refine ⟨5392636234467069050790691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7190181645956092067720921 5392636234467069050790691)
          ·
            refine ⟨8088954351700603576186037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392636234467069050790691 8088954351700603576186037)
            ·
              refine ⟨758339470471931585267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8088954351700603576186037 758339470471931585267441)
              ·
                refine ⟨568754602853948688950581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758339470471931585267441 568754602853948688950581)
                ·
                  refine ⟨53320744017557689589117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568754602853948688950581 53320744017557689589117)
                  ·
                    refine ⟨19995279006584133595919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53320744017557689589117 19995279006584133595919)
                    ·
                      rfl

theorem cell22_58411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].length) (baseStart_58411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58411 prefixEnd_58411 := by exact prefixLift 58411
  have htrace : WordTrace (prefixWord ++ tailWord_58411) baseStart_58411 baseEnd_58411 := by
    simpa [prefixWord, tailWord_58411, baseEnd_58411] using wordTrace_append hprefix tailTrace_58411
  have hstable : (prefixWord ++ tailWord_58411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58411).length < 2 ^ (prefixWord ++ tailWord_58411).sum := by decide
  have hdescent : baseEnd_58411 < baseStart_58411 := by decide
  rcases family_descends (prefixWord ++ tailWord_58411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58428 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_58428 : Nat := 118140960795 + 58428 * 2 ^ 59
def prefixEnd_58428 : Nat := 4983230072969 + 3 ^ 40 * 58428 * 2
def baseEnd_58428 : Nat := 20001098454001755920867

theorem tailTrace_58428 : CollatzResearch.WordTrace tailWord_58428 prefixEnd_58428 20001098454001755920867 := by
  unfold tailWord_58428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065522116166404776531969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1420696154888539702042625 1065522116166404776531969)
  ·
    refine ⟨799141587124803582398977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1065522116166404776531969 799141587124803582398977)
    ·
      refine ⟨599356190343602686799233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 799141587124803582398977 599356190343602686799233)
      ·
        refine ⟨449517142757702015099425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599356190343602686799233 449517142757702015099425)
        ·
          refine ⟨337137857068276511324569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449517142757702015099425 337137857068276511324569)
          ·
            refine ⟨252853392801207383493427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337137857068276511324569 252853392801207383493427)
            ·
              refine ⟨379280089201811075240141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252853392801207383493427 379280089201811075240141)
              ·
                refine ⟨142230033450679153215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379280089201811075240141 142230033450679153215053)
                ·
                  refine ⟨53336262544004682455645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142230033450679153215053 53336262544004682455645)
                  ·
                    refine ⟨20001098454001755920867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53336262544004682455645 20001098454001755920867)
                    ·
                      rfl

theorem cell22_58428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_58428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58428 prefixEnd_58428 := by exact prefixLift 58428
  have htrace : WordTrace (prefixWord ++ tailWord_58428) baseStart_58428 baseEnd_58428 := by
    simpa [prefixWord, tailWord_58428, baseEnd_58428] using wordTrace_append hprefix tailTrace_58428
  have hstable : (prefixWord ++ tailWord_58428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58428).length < 2 ^ (prefixWord ++ tailWord_58428).sum := by decide
  have hdescent : baseEnd_58428 < baseStart_58428 := by decide
  rcases family_descends (prefixWord ++ tailWord_58428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58445 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_58445 : Nat := 118140960795 + 58445 * 2 ^ 59
def prefixEnd_58445 : Nat := 4983230072969 + 3 ^ 40 * 58445 * 2
def baseEnd_58445 : Nat := 20006917901419378245815

theorem tailTrace_58445 : CollatzResearch.WordTrace tailWord_58445 prefixEnd_58445 20006917901419378245815 := by
  unfold tailWord_58445
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131664273271221456432789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1421109515514147637621859 2131664273271221456432789)
  ·
    refine ⟨99921762809588505770287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2131664273271221456432789 99921762809588505770287)
    ·
      refine ⟨149882644214382758655431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99921762809588505770287 149882644214382758655431)
      ·
        refine ⟨224823966321574137983147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149882644214382758655431 224823966321574137983147)
        ·
          refine ⟨337235949482361206974721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224823966321574137983147 337235949482361206974721)
          ·
            refine ⟨252926962111770905231041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337235949482361206974721 252926962111770905231041)
            ·
              refine ⟨189695221583828178923281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252926962111770905231041 189695221583828178923281)
              ·
                refine ⟨142271416187871134192461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189695221583828178923281 142271416187871134192461)
                ·
                  refine ⟨53351781070451675322173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142271416187871134192461 53351781070451675322173)
                  ·
                    refine ⟨20006917901419378245815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53351781070451675322173 20006917901419378245815)
                    ·
                      rfl

theorem cell22_58445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_58445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58445 prefixEnd_58445 := by exact prefixLift 58445
  have htrace : WordTrace (prefixWord ++ tailWord_58445) baseStart_58445 baseEnd_58445 := by
    simpa [prefixWord, tailWord_58445, baseEnd_58445] using wordTrace_append hprefix tailTrace_58445
  have hstable : (prefixWord ++ tailWord_58445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58445).length < 2 ^ (prefixWord ++ tailWord_58445).sum := by decide
  have hdescent : baseEnd_58445 < baseStart_58445 := by decide
  rcases family_descends (prefixWord ++ tailWord_58445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58505 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_58505 : Nat := 118140960795 + 58505 * 2 ^ 59
def prefixEnd_58505 : Nat := 4983230072969 + 3 ^ 40 * 58505 * 2
def baseEnd_58505 : Nat := 20027457127599221745631

theorem tailTrace_58505 : CollatzResearch.WordTrace tailWord_58505 prefixEnd_58505 20027457127599221745631 := by
  unfold tailWord_58505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133852653053851703616969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1422568435369234469077979 2133852653053851703616969)
  ·
    refine ⟨1600389489790388777712727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2133852653053851703616969 1600389489790388777712727)
    ·
      refine ⟨2400584234685583166569091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600389489790388777712727 2400584234685583166569091)
      ·
        refine ⟨3600876352028374749853637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400584234685583166569091 3600876352028374749853637)
        ·
          refine ⟨675164316005320265597557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3600876352028374749853637 675164316005320265597557)
          ·
            refine ⟨63296654625498774899771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 675164316005320265597557 63296654625498774899771)
            ·
              refine ⟨94944981938248162349657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63296654625498774899771 94944981938248162349657)
              ·
                refine ⟨71208736453686121762243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94944981938248162349657 71208736453686121762243)
                ·
                  refine ⟨106813104680529182643365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71208736453686121762243 106813104680529182643365)
                  ·
                    refine ⟨20027457127599221745631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106813104680529182643365 20027457127599221745631)
                    ·
                      rfl

theorem cell22_58505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_58505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58505 prefixEnd_58505 := by exact prefixLift 58505
  have htrace : WordTrace (prefixWord ++ tailWord_58505) baseStart_58505 baseEnd_58505 := by
    simpa [prefixWord, tailWord_58505, baseEnd_58505] using wordTrace_append hprefix tailTrace_58505
  have hstable : (prefixWord ++ tailWord_58505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58505).length < 2 ^ (prefixWord ++ tailWord_58505).sum := by decide
  have hdescent : baseEnd_58505 < baseStart_58505 := by decide
  rcases family_descends (prefixWord ++ tailWord_58505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58522 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_58522 : Nat := 118140960795 + 58522 * 2 ^ 59
def prefixEnd_58522 : Nat := 4983230072969 + 3 ^ 40 * 58522 * 2
def baseEnd_58522 : Nat := 20033276575016844070579

theorem tailTrace_58522 : CollatzResearch.WordTrace tailWord_58522 prefixEnd_58522 20033276575016844070579 := by
  unfold tailWord_58522
  simp only [CollatzResearch.WordTrace]
  refine ⟨533618173498065901746455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1422981795994842404657213 533618173498065901746455)
  ·
    refine ⟨800427260247098852619683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533618173498065901746455 800427260247098852619683)
    ·
      refine ⟨1200640890370648278929525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800427260247098852619683 1200640890370648278929525)
      ·
        refine ⟨112560083472248276149643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1200640890370648278929525 112560083472248276149643)
        ·
          refine ⟨168840125208372414224465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112560083472248276149643 168840125208372414224465)
          ·
            refine ⟨126630093906279310668349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168840125208372414224465 126630093906279310668349)
            ·
              refine ⟨47486285214854741500631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126630093906279310668349 47486285214854741500631)
              ·
                refine ⟨71229427822282112250947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47486285214854741500631 71229427822282112250947)
                ·
                  refine ⟨106844141733423168376421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71229427822282112250947 106844141733423168376421)
                  ·
                    refine ⟨20033276575016844070579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106844141733423168376421 20033276575016844070579)
                    ·
                      rfl

theorem cell22_58522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_58522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58522 prefixEnd_58522 := by exact prefixLift 58522
  have htrace : WordTrace (prefixWord ++ tailWord_58522) baseStart_58522 baseEnd_58522 := by
    simpa [prefixWord, tailWord_58522, baseEnd_58522] using wordTrace_append hprefix tailTrace_58522
  have hstable : (prefixWord ++ tailWord_58522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58522).length < 2 ^ (prefixWord ++ tailWord_58522).sum := by decide
  have hdescent : baseEnd_58522 < baseStart_58522 := by decide
  rcases family_descends (prefixWord ++ tailWord_58522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58533 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_58533 : Nat := 118140960795 + 58533 * 2 ^ 59
def prefixEnd_58533 : Nat := 4983230072969 + 3 ^ 40 * 58533 * 2
def baseEnd_58533 : Nat := 20037042099816482045545

theorem tailTrace_58533 : CollatzResearch.WordTrace tailWord_58533 prefixEnd_58533 20037042099816482045545 := by
  unfold tailWord_58533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134873896952412485636253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1423249264634941657090835 2134873896952412485636253)
  ·
    refine ⟨800577711357154682113595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2134873896952412485636253 800577711357154682113595)
    ·
      refine ⟨1200866567035732023170393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800577711357154682113595 1200866567035732023170393)
      ·
        refine ⟨900649925276799017377795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200866567035732023170393 900649925276799017377795)
        ·
          refine ⟨1350974887915198526066693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900649925276799017377795 1350974887915198526066693)
          ·
            refine ⟨253307791484099723637505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1350974887915198526066693 253307791484099723637505)
            ·
              refine ⟨189980843613074792728129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253307791484099723637505 189980843613074792728129)
              ·
                refine ⟨142485632709806094546097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189980843613074792728129 142485632709806094546097)
                ·
                  refine ⟨106864224532354570909573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142485632709806094546097 106864224532354570909573)
                  ·
                    refine ⟨20037042099816482045545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106864224532354570909573 20037042099816482045545)
                    ·
                      rfl

theorem cell22_58533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_58533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58533 prefixEnd_58533 := by exact prefixLift 58533
  have htrace : WordTrace (prefixWord ++ tailWord_58533) baseStart_58533 baseEnd_58533 := by
    simpa [prefixWord, tailWord_58533, baseEnd_58533] using wordTrace_append hprefix tailTrace_58533
  have hstable : (prefixWord ++ tailWord_58533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58533).length < 2 ^ (prefixWord ++ tailWord_58533).sum := by decide
  have hdescent : baseEnd_58533 < baseStart_58533 := by decide
  rcases family_descends (prefixWord ++ tailWord_58533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58573 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_58573 : Nat := 118140960795 + 58573 * 2 ^ 59
def prefixEnd_58573 : Nat := 4983230072969 + 3 ^ 40 * 58573 * 2
def baseEnd_58573 : Nat := 20050734917269711045423

theorem tailTrace_58573 : CollatzResearch.WordTrace tailWord_58573 prefixEnd_58573 20050734917269711045423 := by
  unfold tailWord_58573
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136332816807499317092373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1424221877871666211394915 2136332816807499317092373)
  ·
    refine ⟨100140600787851530488705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2136332816807499317092373 100140600787851530488705)
    ·
      refine ⟨75105450590888647866529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100140600787851530488705 75105450590888647866529)
      ·
        refine ⟨56329087943166485899897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75105450590888647866529 56329087943166485899897)
        ·
          refine ⟨42246815957374864424923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56329087943166485899897 42246815957374864424923)
          ·
            refine ⟨63370223936062296637385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42246815957374864424923 63370223936062296637385)
            ·
              refine ⟨47527667952046722478039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63370223936062296637385 47527667952046722478039)
              ·
                refine ⟨71291501928070083717059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47527667952046722478039 71291501928070083717059)
                ·
                  refine ⟨106937252892105125575589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71291501928070083717059 106937252892105125575589)
                  ·
                    refine ⟨20050734917269711045423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106937252892105125575589 20050734917269711045423)
                    ·
                      rfl

theorem cell22_58573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_58573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58573 prefixEnd_58573 := by exact prefixLift 58573
  have htrace : WordTrace (prefixWord ++ tailWord_58573) baseStart_58573 baseEnd_58573 := by
    simpa [prefixWord, tailWord_58573, baseEnd_58573] using wordTrace_append hprefix tailTrace_58573
  have hstable : (prefixWord ++ tailWord_58573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58573).length < 2 ^ (prefixWord ++ tailWord_58573).sum := by decide
  have hdescent : baseEnd_58573 < baseStart_58573 := by decide
  rcases family_descends (prefixWord ++ tailWord_58573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58593 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 7]
def baseStart_58593 : Nat := 118140960795 + 58593 * 2 ^ 59
def prefixEnd_58593 : Nat := 4983230072969 + 3 ^ 40 * 58593 * 2
def baseEnd_58593 : Nat := 6685860441998775181787

theorem tailTrace_58593 : CollatzResearch.WordTrace tailWord_58593 prefixEnd_58593 6685860441998775181787 := by
  unfold tailWord_58593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137062276735042732820433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1424708184490028488546955 2137062276735042732820433)
  ·
    refine ⟨1602796707551282049615325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2137062276735042732820433 1602796707551282049615325)
    ·
      refine ⟨601048765331730768605747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1602796707551282049615325 601048765331730768605747)
      ·
        refine ⟨901573147997596152908621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601048765331730768605747 901573147997596152908621)
        ·
          refine ⟨338089930499098557340733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 901573147997596152908621 338089930499098557340733)
          ·
            refine ⟨126783723937161959002775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338089930499098557340733 126783723937161959002775)
            ·
              refine ⟨190175585905742938504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126783723937161959002775 190175585905742938504163)
              ·
                refine ⟨285263378858614407756245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190175585905742938504163 285263378858614407756245)
                ·
                  refine ⟨6685860441998775181787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285263378858614407756245 6685860441998775181787)
                  ·
                    rfl

theorem cell22_58593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_58593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58593 prefixEnd_58593 := by exact prefixLift 58593
  have htrace : WordTrace (prefixWord ++ tailWord_58593) baseStart_58593 baseEnd_58593 := by
    simpa [prefixWord, tailWord_58593, baseEnd_58593] using wordTrace_append hprefix tailTrace_58593
  have hstable : (prefixWord ++ tailWord_58593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58593).length < 2 ^ (prefixWord ++ tailWord_58593).sum := by decide
  have hdescent : baseEnd_58593 < baseStart_58593 := by decide
  rcases family_descends (prefixWord ++ tailWord_58593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58597 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_58597 : Nat := 118140960795 + 58597 * 2 ^ 59
def prefixEnd_58597 : Nat := 4983230072969 + 3 ^ 40 * 58597 * 2
def baseEnd_58597 : Nat := 20058950607741648445349

theorem tailTrace_58597 : CollatzResearch.WordTrace tailWord_58597 prefixEnd_58597 20058950607741648445349 := by
  unfold tailWord_58597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137208168720551415966045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1424805445813700943977363 2137208168720551415966045)
  ·
    refine ⟨801453063270206780987267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2137208168720551415966045 801453063270206780987267)
    ·
      refine ⟨1202179594905310171480901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801453063270206780987267 1202179594905310171480901)
      ·
        refine ⟨225408674044745657152669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1202179594905310171480901 225408674044745657152669)
        ·
          refine ⟨84528252766779621432251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225408674044745657152669 84528252766779621432251)
          ·
            refine ⟨126792379150169432148377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84528252766779621432251 126792379150169432148377)
            ·
              refine ⟨95094284362627074111283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126792379150169432148377 95094284362627074111283)
              ·
                refine ⟨142641426543940611166925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95094284362627074111283 142641426543940611166925)
                ·
                  refine ⟨53490534953977729187597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142641426543940611166925 53490534953977729187597)
                  ·
                    refine ⟨20058950607741648445349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53490534953977729187597 20058950607741648445349)
                    ·
                      rfl

theorem cell22_58597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_58597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58597 prefixEnd_58597 := by exact prefixLift 58597
  have htrace : WordTrace (prefixWord ++ tailWord_58597) baseStart_58597 baseEnd_58597 := by
    simpa [prefixWord, tailWord_58597, baseEnd_58597] using wordTrace_append hprefix tailTrace_58597
  have hstable : (prefixWord ++ tailWord_58597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58597).length < 2 ^ (prefixWord ++ tailWord_58597).sum := by decide
  have hdescent : baseEnd_58597 < baseStart_58597 := by decide
  rcases family_descends (prefixWord ++ tailWord_58597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58668 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_58668 : Nat := 118140960795 + 58668 * 2 ^ 59
def prefixEnd_58668 : Nat := 4983230072969 + 3 ^ 40 * 58668 * 2
def baseEnd_58668 : Nat := 20083255358721129920131

theorem tailTrace_58668 : CollatzResearch.WordTrace tailWord_58668 prefixEnd_58668 20083255358721129920131 := by
  unfold tailWord_58668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069898875731665270900329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1426531834308887027867105 1069898875731665270900329)
  ·
    refine ⟨802424156798748953175247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1069898875731665270900329 802424156798748953175247)
    ·
      refine ⟨1203636235198123429762871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802424156798748953175247 1203636235198123429762871)
      ·
        refine ⟨1805454352797185144644307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203636235198123429762871 1805454352797185144644307)
        ·
          refine ⟨2708181529195777716966461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805454352797185144644307 2708181529195777716966461)
          ·
            refine ⟨1015568073448416643862423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2708181529195777716966461 1015568073448416643862423)
            ·
              refine ⟨1523352110172624965793635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015568073448416643862423 1523352110172624965793635)
              ·
                refine ⟨2285028165258937448690453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523352110172624965793635 2285028165258937448690453)
                ·
                  refine ⟨107110695246512692907365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2285028165258937448690453 107110695246512692907365)
                  ·
                    refine ⟨20083255358721129920131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107110695246512692907365 20083255358721129920131)
                    ·
                      rfl

theorem cell22_58668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_58668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58668 prefixEnd_58668 := by exact prefixLift 58668
  have htrace : WordTrace (prefixWord ++ tailWord_58668) baseStart_58668 baseEnd_58668 := by
    simpa [prefixWord, tailWord_58668, baseEnd_58668] using wordTrace_append hprefix tailTrace_58668
  have hstable : (prefixWord ++ tailWord_58668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58668).length < 2 ^ (prefixWord ++ tailWord_58668).sum := by decide
  have hdescent : baseEnd_58668 < baseStart_58668 := by decide
  rcases family_descends (prefixWord ++ tailWord_58668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58713 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_58713 : Nat := 118140960795 + 58713 * 2 ^ 59
def prefixEnd_58713 : Nat := 4983230072969 + 3 ^ 40 * 58713 * 2
def baseEnd_58713 : Nat := 20098659778356012544993

theorem tailTrace_58713 : CollatzResearch.WordTrace tailWord_58713 prefixEnd_58713 20098659778356012544993 := by
  unfold tailWord_58713
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141439036300303227188793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1427626024200202151459195 2141439036300303227188793)
  ·
    refine ⟨1606079277225227420391595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2141439036300303227188793 1606079277225227420391595)
    ·
      refine ⟨2409118915837841130587393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606079277225227420391595 2409118915837841130587393)
      ·
        refine ⟨1806839186878380847940545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409118915837841130587393 1806839186878380847940545)
        ·
          refine ⟨1355129390158785635955409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806839186878380847940545 1355129390158785635955409)
          ·
            refine ⟨1016347042619089226966557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355129390158785635955409 1016347042619089226966557)
            ·
              refine ⟨381130140982158460112459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016347042619089226966557 381130140982158460112459)
              ·
                refine ⟨571695211473237690168689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381130140982158460112459 571695211473237690168689)
                ·
                  refine ⟨428771408604928267626517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571695211473237690168689 428771408604928267626517)
                  ·
                    refine ⟨20098659778356012544993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 428771408604928267626517 20098659778356012544993)
                    ·
                      rfl

theorem cell22_58713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_58713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58713 prefixEnd_58713 := by exact prefixLift 58713
  have htrace : WordTrace (prefixWord ++ tailWord_58713) baseStart_58713 baseEnd_58713 := by
    simpa [prefixWord, tailWord_58713, baseEnd_58713] using wordTrace_append hprefix tailTrace_58713
  have hstable : (prefixWord ++ tailWord_58713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58713).length < 2 ^ (prefixWord ++ tailWord_58713).sum := by decide
  have hdescent : baseEnd_58713 < baseStart_58713 := by decide
  rcases family_descends (prefixWord ++ tailWord_58713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58732 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_58732 : Nat := 118140960795 + 58732 * 2 ^ 59
def prefixEnd_58732 : Nat := 4983230072969 + 3 ^ 40 * 58732 * 2
def baseEnd_58732 : Nat := 20105163866646296319935

theorem tailTrace_58732 : CollatzResearch.WordTrace tailWord_58732 prefixEnd_58732 20105163866646296319935 := by
  unfold tailWord_58732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071066011615734736065225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1428088015487646314753633 1071066011615734736065225)
  ·
    refine ⟨803299508711801052048919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071066011615734736065225 803299508711801052048919)
    ·
      refine ⟨1204949263067701578073379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803299508711801052048919 1204949263067701578073379)
      ·
        refine ⟨1807423894601552367110069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204949263067701578073379 1807423894601552367110069)
        ·
          refine ⟨169445990118895534416569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1807423894601552367110069 169445990118895534416569)
          ·
            refine ⟨127084492589171650812427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169445990118895534416569 127084492589171650812427)
            ·
              refine ⟨190626738883757476218641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127084492589171650812427 190626738883757476218641)
              ·
                refine ⟨142970054162818107163981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190626738883757476218641 142970054162818107163981)
                ·
                  refine ⟨53613770311056790186493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142970054162818107163981 53613770311056790186493)
                  ·
                    refine ⟨20105163866646296319935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53613770311056790186493 20105163866646296319935)
                    ·
                      rfl

theorem cell22_58732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_58732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58732 prefixEnd_58732 := by exact prefixLift 58732
  have htrace : WordTrace (prefixWord ++ tailWord_58732) baseStart_58732 baseEnd_58732 := by
    simpa [prefixWord, tailWord_58732, baseEnd_58732] using wordTrace_append hprefix tailTrace_58732
  have hstable : (prefixWord ++ tailWord_58732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58732).length < 2 ^ (prefixWord ++ tailWord_58732).sum := by decide
  have hdescent : baseEnd_58732 < baseStart_58732 := by decide
  rcases family_descends (prefixWord ++ tailWord_58732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58734 : List Nat := [4, 1, 2, 4, 1, 1, 3, 6]
def baseStart_58734 : Nat := 118140960795 + 58734 * 2 ^ 59
def prefixEnd_58734 : Nat := 4983230072969 + 3 ^ 40 * 58734 * 2
def baseEnd_58734 : Nat := 2233983167502106418881

theorem tailTrace_58734 : CollatzResearch.WordTrace tailWord_58734 prefixEnd_58734 2233983167502106418881 := by
  unfold tailWord_58734
  simp only [CollatzResearch.WordTrace]
  refine ⟨267775621153027976712907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1428136646149482542468837 267775621153027976712907)
  ·
    refine ⟨401663431729541965069361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267775621153027976712907 401663431729541965069361)
    ·
      refine ⟨301247573797156473802021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401663431729541965069361 301247573797156473802021)
      ·
        refine ⟨56483920086966838837879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301247573797156473802021 56483920086966838837879)
        ·
          refine ⟨84725880130450258256819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56483920086966838837879 84725880130450258256819)
          ·
            refine ⟨127088820195675387385229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84725880130450258256819 127088820195675387385229)
            ·
              refine ⟨47658307573378270269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127088820195675387385229 47658307573378270269461)
              ·
                refine ⟨2233983167502106418881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47658307573378270269461 2233983167502106418881)
                ·
                  rfl

theorem cell22_58734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_58734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58734 prefixEnd_58734 := by exact prefixLift 58734
  have htrace : WordTrace (prefixWord ++ tailWord_58734) baseStart_58734 baseEnd_58734 := by
    simpa [prefixWord, tailWord_58734, baseEnd_58734] using wordTrace_append hprefix tailTrace_58734
  have hstable : (prefixWord ++ tailWord_58734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58734).length < 2 ^ (prefixWord ++ tailWord_58734).sum := by decide
  have hdescent : baseEnd_58734 < baseStart_58734 := by decide
  rcases family_descends (prefixWord ++ tailWord_58734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58743 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_58743 : Nat := 118140960795 + 58743 * 2 ^ 59
def prefixEnd_58743 : Nat := 4983230072969 + 3 ^ 40 * 58743 * 2
def baseEnd_58743 : Nat := 20108929391445934294901

theorem tailTrace_58743 : CollatzResearch.WordTrace tailWord_58743 prefixEnd_58743 20108929391445934294901 := by
  unfold tailWord_58743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142533226191618350780883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1428355484127745567187255 2142533226191618350780883)
  ·
    refine ⟨3213799839287427526171325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142533226191618350780883 3213799839287427526171325)
    ·
      refine ⟨1205174939732785322314247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3213799839287427526171325 1205174939732785322314247)
      ·
        refine ⟨1807762409599177983471371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205174939732785322314247 1807762409599177983471371)
        ·
          refine ⟨2711643614398766975207057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807762409599177983471371 2711643614398766975207057)
          ·
            refine ⟨2033732710799075231405293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711643614398766975207057 2033732710799075231405293)
            ·
              refine ⟨762649766549653211776985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2033732710799075231405293 762649766549653211776985)
              ·
                refine ⟨571987324912239908832739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762649766549653211776985 571987324912239908832739)
                ·
                  refine ⟨857980987368359863249109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571987324912239908832739 857980987368359863249109)
                  ·
                    refine ⟨20108929391445934294901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 857980987368359863249109 20108929391445934294901)
                    ·
                      rfl

theorem cell22_58743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_58743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58743 prefixEnd_58743 := by exact prefixLift 58743
  have htrace : WordTrace (prefixWord ++ tailWord_58743) baseStart_58743 baseEnd_58743 := by
    simpa [prefixWord, tailWord_58743, baseEnd_58743] using wordTrace_append hprefix tailTrace_58743
  have hstable : (prefixWord ++ tailWord_58743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58743).length < 2 ^ (prefixWord ++ tailWord_58743).sum := by decide
  have hdescent : baseEnd_58743 < baseStart_58743 := by decide
  rcases family_descends (prefixWord ++ tailWord_58743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58749 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_58749 : Nat := 118140960795 + 58749 * 2 ^ 59
def prefixEnd_58749 : Nat := 4983230072969 + 3 ^ 40 * 58749 * 2
def baseEnd_58749 : Nat := 20110983314063918644883

theorem tailTrace_58749 : CollatzResearch.WordTrace tailWord_58749 prefixEnd_58749 20110983314063918644883 := by
  unfold tailWord_58749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142752064169881375499301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1428501376113254250332867 2142752064169881375499301)
  ·
    refine ⟨401766012031852757906119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2142752064169881375499301 401766012031852757906119)
    ·
      refine ⟨602649018047779136859179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401766012031852757906119 602649018047779136859179)
      ·
        refine ⟨903973527071668705288769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602649018047779136859179 903973527071668705288769)
        ·
          refine ⟨677980145303751528966577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903973527071668705288769 677980145303751528966577)
          ·
            refine ⟨508485108977813646724933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677980145303751528966577 508485108977813646724933)
            ·
              refine ⟨95340957933340058760925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508485108977813646724933 95340957933340058760925)
              ·
                refine ⟨35752859225002522035347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95340957933340058760925 35752859225002522035347)
                ·
                  refine ⟨53629288837503783053021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35752859225002522035347 53629288837503783053021)
                  ·
                    refine ⟨20110983314063918644883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53629288837503783053021 20110983314063918644883)
                    ·
                      rfl

theorem cell22_58749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_58749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58749 prefixEnd_58749 := by exact prefixLift 58749
  have htrace : WordTrace (prefixWord ++ tailWord_58749) baseStart_58749 baseEnd_58749 := by
    simpa [prefixWord, tailWord_58749, baseEnd_58749] using wordTrace_append hprefix tailTrace_58749
  have hstable : (prefixWord ++ tailWord_58749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58749).length < 2 ^ (prefixWord ++ tailWord_58749).sum := by decide
  have hdescent : baseEnd_58749 < baseStart_58749 := by decide
  rcases family_descends (prefixWord ++ tailWord_58749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58760 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_58760 : Nat := 118140960795 + 58760 * 2 ^ 59
def prefixEnd_58760 : Nat := 4983230072969 + 3 ^ 40 * 58760 * 2
def baseEnd_58760 : Nat := 20114748838863556619849

theorem tailTrace_58760 : CollatzResearch.WordTrace tailWord_58760 prefixEnd_58760 20114748838863556619849 := by
  unfold tailWord_58760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071576633565015127074867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1428768844753353502766489 1071576633565015127074867)
  ·
    refine ⟨1607364950347522690612301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1071576633565015127074867 1607364950347522690612301)
    ·
      refine ⟨602761856380321008979613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1607364950347522690612301 602761856380321008979613)
      ·
        refine ⟨226035696142620378367355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602761856380321008979613 226035696142620378367355)
        ·
          refine ⟨339053544213930567551033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226035696142620378367355 339053544213930567551033)
          ·
            refine ⟨254290158160447925663275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339053544213930567551033 254290158160447925663275)
            ·
              refine ⟨381435237240671888494913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254290158160447925663275 381435237240671888494913)
              ·
                refine ⟨286076427930503916371185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381435237240671888494913 286076427930503916371185)
                ·
                  refine ⟨214557320947877937278389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286076427930503916371185 214557320947877937278389)
                  ·
                    refine ⟨20114748838863556619849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214557320947877937278389 20114748838863556619849)
                    ·
                      rfl

theorem cell22_58760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_58760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58760 prefixEnd_58760 := by exact prefixLift 58760
  have htrace : WordTrace (prefixWord ++ tailWord_58760) baseStart_58760 baseEnd_58760 := by
    simpa [prefixWord, tailWord_58760, baseEnd_58760] using wordTrace_append hprefix tailTrace_58760
  have hstable : (prefixWord ++ tailWord_58760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58760).length < 2 ^ (prefixWord ++ tailWord_58760).sum := by decide
  have hdescent : baseEnd_58760 < baseStart_58760 := by decide
  rcases family_descends (prefixWord ++ tailWord_58760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58824 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_58824 : Nat := 118140960795 + 58824 * 2 ^ 59
def prefixEnd_58824 : Nat := 4983230072969 + 3 ^ 40 * 58824 * 2
def baseEnd_58824 : Nat := 6712219115596241006551

theorem tailTrace_58824 : CollatzResearch.WordTrace tailWord_58824 prefixEnd_58824 6712219115596241006551 := by
  unfold tailWord_58824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072743769449084592239763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1430325025932112789653017 1072743769449084592239763)
  ·
    refine ⟨1609115654173626888359645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1072743769449084592239763 1609115654173626888359645)
    ·
      refine ⟨603418370315110083134867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1609115654173626888359645 603418370315110083134867)
      ·
        refine ⟨905127555472665124702301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603418370315110083134867 905127555472665124702301)
        ·
          refine ⟨339422833302249421763363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905127555472665124702301 339422833302249421763363)
          ·
            refine ⟨509134249953374132645045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339422833302249421763363 509134249953374132645045)
            ·
              refine ⟨47731335933128824935473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509134249953374132645045 47731335933128824935473)
              ·
                refine ⟨35798501949846618701605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47731335933128824935473 35798501949846618701605)
                ·
                  refine ⟨6712219115596241006551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35798501949846618701605 6712219115596241006551)
                  ·
                    rfl

theorem cell22_58824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_58824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_58824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_58824 prefixEnd_58824 := by exact prefixLift 58824
  have htrace : WordTrace (prefixWord ++ tailWord_58824) baseStart_58824 baseEnd_58824 := by
    simpa [prefixWord, tailWord_58824, baseEnd_58824] using wordTrace_append hprefix tailTrace_58824
  have hstable : (prefixWord ++ tailWord_58824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58824).length < 2 ^ (prefixWord ++ tailWord_58824).sum := by decide
  have hdescent : baseEnd_58824 < baseStart_58824 := by decide
  rcases family_descends (prefixWord ++ tailWord_58824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59053 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_59053 : Nat := 118140960795 + 59053 * 2 ^ 59
def prefixEnd_59053 : Nat := 4983230072969 + 3 ^ 40 * 59053 * 2
def baseEnd_59053 : Nat := 20215048726708459043951

theorem tailTrace_59053 : CollatzResearch.WordTrace tailWord_59053 prefixEnd_59053 20215048726708459043951 := by
  unfold tailWord_59053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153839855068541294565813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1435893236712360863043875 2153839855068541294565813)
  ·
    refine ⟨201922486412675746365545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2153839855068541294565813 201922486412675746365545)
    ·
      refine ⟨151441864809506809774159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201922486412675746365545 151441864809506809774159)
      ·
        refine ⟨227162797214260214661239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151441864809506809774159 227162797214260214661239)
        ·
          refine ⟨340744195821390321991859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227162797214260214661239 340744195821390321991859)
          ·
            refine ⟨511116293732085482987789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340744195821390321991859 511116293732085482987789)
            ·
              refine ⟨191668610149532056120421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511116293732085482987789 191668610149532056120421)
              ·
                refine ⟨35937864403037260522579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191668610149532056120421 35937864403037260522579)
                ·
                  refine ⟨53906796604555890783869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35937864403037260522579 53906796604555890783869)
                  ·
                    refine ⟨20215048726708459043951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53906796604555890783869 20215048726708459043951)
                    ·
                      rfl

theorem cell22_59053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_59053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59053 prefixEnd_59053 := by exact prefixLift 59053
  have htrace : WordTrace (prefixWord ++ tailWord_59053) baseStart_59053 baseEnd_59053 := by
    simpa [prefixWord, tailWord_59053, baseEnd_59053] using wordTrace_append hprefix tailTrace_59053
  have hstable : (prefixWord ++ tailWord_59053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59053).length < 2 ^ (prefixWord ++ tailWord_59053).sum := by decide
  have hdescent : baseEnd_59053 < baseStart_59053 := by decide
  rcases family_descends (prefixWord ++ tailWord_59053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59077 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 6]
def baseStart_59077 : Nat := 118140960795 + 59077 * 2 ^ 59
def prefixEnd_59077 : Nat := 4983230072969 + 3 ^ 40 * 59077 * 2
def baseEnd_59077 : Nat := 6741088139060132147959

theorem tailTrace_59077 : CollatzResearch.WordTrace tailWord_59077 prefixEnd_59077 6741088139060132147959 := by
  unfold tailWord_59077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154715206981593393439485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1436476804654395595626323 2154715206981593393439485)
  ·
    refine ⟨808018202618097522539807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2154715206981593393439485 808018202618097522539807)
    ·
      refine ⟨1212027303927146283809711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808018202618097522539807 1212027303927146283809711)
      ·
        refine ⟨1818040955890719425714567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212027303927146283809711 1818040955890719425714567)
        ·
          refine ⟨2727061433836079138571851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818040955890719425714567 2727061433836079138571851)
          ·
            refine ⟨4090592150754118707857777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727061433836079138571851 4090592150754118707857777)
            ·
              refine ⟨3067944113065589030893333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090592150754118707857777 3067944113065589030893333)
              ·
                refine ⟨143809880299949485823125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3067944113065589030893333 143809880299949485823125)
                ·
                  refine ⟨6741088139060132147959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143809880299949485823125 6741088139060132147959)
                  ·
                    rfl

theorem cell22_59077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_59077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59077 prefixEnd_59077 := by exact prefixLift 59077
  have htrace : WordTrace (prefixWord ++ tailWord_59077) baseStart_59077 baseEnd_59077 := by
    simpa [prefixWord, tailWord_59077, baseEnd_59077] using wordTrace_append hprefix tailTrace_59077
  have hstable : (prefixWord ++ tailWord_59077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59077).length < 2 ^ (prefixWord ++ tailWord_59077).sum := by decide
  have hdescent : baseEnd_59077 < baseStart_59077 := by decide
  rcases family_descends (prefixWord ++ tailWord_59077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59079 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 1, 4]
def baseStart_59079 : Nat := 118140960795 + 59079 * 2 ^ 59
def prefixEnd_59079 : Nat := 4983230072969 + 3 ^ 40 * 59079 * 2
def baseEnd_59079 : Nat := 20223949058053057893871

theorem tailTrace_59079 : CollatzResearch.WordTrace tailWord_59079 prefixEnd_59079 20223949058053057893871 := by
  unfold tailWord_59079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154788152974347735012291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1436525435316231823341527 2154788152974347735012291)
  ·
    refine ⟨3232182229461521602518437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154788152974347735012291 3232182229461521602518437)
    ·
      refine ⟨606034168024035300472207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3232182229461521602518437 606034168024035300472207)
      ·
        refine ⟨909051252036052950708311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606034168024035300472207 909051252036052950708311)
        ·
          refine ⟨1363576878054079426062467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909051252036052950708311 1363576878054079426062467)
          ·
            refine ⟨2045365317081119139093701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363576878054079426062467 2045365317081119139093701)
            ·
              refine ⟨383505996952709838580069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2045365317081119139093701 383505996952709838580069)
              ·
                refine ⟨71907374428633094733763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383505996952709838580069 71907374428633094733763)
                ·
                  refine ⟨107861061642949642100645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71907374428633094733763 107861061642949642100645)
                  ·
                    refine ⟨20223949058053057893871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107861061642949642100645 20223949058053057893871)
                    ·
                      rfl

theorem cell22_59079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_59079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59079 prefixEnd_59079 := by exact prefixLift 59079
  have htrace : WordTrace (prefixWord ++ tailWord_59079) baseStart_59079 baseEnd_59079 := by
    simpa [prefixWord, tailWord_59079, baseEnd_59079] using wordTrace_append hprefix tailTrace_59079
  have hstable : (prefixWord ++ tailWord_59079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59079).length < 2 ^ (prefixWord ++ tailWord_59079).sum := by decide
  have hdescent : baseEnd_59079 < baseStart_59079 := by decide
  rcases family_descends (prefixWord ++ tailWord_59079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59100 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_59100 : Nat := 118140960795 + 59100 * 2 ^ 59
def prefixEnd_59100 : Nat := 4983230072969 + 3 ^ 40 * 59100 * 2
def baseEnd_59100 : Nat := 6743712595738667706269

theorem tailTrace_59100 : CollatzResearch.WordTrace tailWord_59100 prefixEnd_59100 6743712595738667706269 := by
  unfold tailWord_59100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077777042949134160763377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1437036057265512214351169 1077777042949134160763377)
  ·
    refine ⟨808332782211850620572533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1077777042949134160763377 808332782211850620572533)
    ·
      refine ⟨75781198332360995678675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 808332782211850620572533 75781198332360995678675)
      ·
        refine ⟨113671797498541493518013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75781198332360995678675 113671797498541493518013)
        ·
          refine ⟨42626924061953060069255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113671797498541493518013 42626924061953060069255)
          ·
            refine ⟨63940386092929590103883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42626924061953060069255 63940386092929590103883)
            ·
              refine ⟨95910579139394385155825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63940386092929590103883 95910579139394385155825)
              ·
                refine ⟨71932934354545788866869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95910579139394385155825 71932934354545788866869)
                ·
                  refine ⟨6743712595738667706269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71932934354545788866869 6743712595738667706269)
                  ·
                    rfl

theorem cell22_59100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_59100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59100 prefixEnd_59100 := by exact prefixLift 59100
  have htrace : WordTrace (prefixWord ++ tailWord_59100) baseStart_59100 baseEnd_59100 := by
    simpa [prefixWord, tailWord_59100, baseEnd_59100] using wordTrace_append hprefix tailTrace_59100
  have hstable : (prefixWord ++ tailWord_59100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59100).length < 2 ^ (prefixWord ++ tailWord_59100).sum := by decide
  have hdescent : baseEnd_59100 < baseStart_59100 := by decide
  rcases family_descends (prefixWord ++ tailWord_59100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59126 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_59126 : Nat := 118140960795 + 59126 * 2 ^ 59
def prefixEnd_59126 : Nat := 4983230072969 + 3 ^ 40 * 59126 * 2
def baseEnd_59126 : Nat := 20240038118560601968727

theorem tailTrace_59126 : CollatzResearch.WordTrace tailWord_59126 prefixEnd_59126 20240038118560601968727 := by
  unfold tailWord_59126
  simp only [CollatzResearch.WordTrace]
  refine ⟨134781398987754672623327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1437668255869383174648821 134781398987754672623327)
  ·
    refine ⟨202172098481632008934991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134781398987754672623327 202172098481632008934991)
    ·
      refine ⟨303258147722448013402487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202172098481632008934991 303258147722448013402487)
      ·
        refine ⟨454887221583672020103731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303258147722448013402487 454887221583672020103731)
        ·
          refine ⟨682330832375508030155597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454887221583672020103731 682330832375508030155597)
          ·
            refine ⟨255874062140815511308349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682330832375508030155597 255874062140815511308349)
            ·
              refine ⟨95952773302805816740631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255874062140815511308349 95952773302805816740631)
              ·
                refine ⟨143929159954208725110947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95952773302805816740631 143929159954208725110947)
                ·
                  refine ⟨215893739931313087666421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143929159954208725110947 215893739931313087666421)
                  ·
                    refine ⟨20240038118560601968727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215893739931313087666421 20240038118560601968727)
                    ·
                      rfl

theorem cell22_59126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_59126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59126 prefixEnd_59126 := by exact prefixLift 59126
  have htrace : WordTrace (prefixWord ++ tailWord_59126) baseStart_59126 baseEnd_59126 := by
    simpa [prefixWord, tailWord_59126, baseEnd_59126] using wordTrace_append hprefix tailTrace_59126
  have hstable : (prefixWord ++ tailWord_59126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59126).length < 2 ^ (prefixWord ++ tailWord_59126).sum := by decide
  have hdescent : baseEnd_59126 < baseStart_59126 := by decide
  rcases family_descends (prefixWord ++ tailWord_59126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59139 : List Nat := [1, 1, 1, 3, 2, 2, 6, 6]
def baseStart_59139 : Nat := 118140960795 + 59139 * 2 ^ 59
def prefixEnd_59139 : Nat := 4983230072969 + 3 ^ 40 * 59139 * 2
def baseEnd_59139 : Nat := 2249387587136989043743

theorem tailTrace_59139 : CollatzResearch.WordTrace tailWord_59139 prefixEnd_59139 2249387587136989043743 := by
  unfold tailWord_59139
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156976532756977982196471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1437984355171318654797647 2156976532756977982196471)
  ·
    refine ⟨3235464799135466973294707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156976532756977982196471 3235464799135466973294707)
    ·
      refine ⟨4853197198703200459942061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235464799135466973294707 4853197198703200459942061)
      ·
        refine ⟨1819948949513700172478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853197198703200459942061 1819948949513700172478273)
        ·
          refine ⟨1364961712135275129358705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819948949513700172478273 1364961712135275129358705)
          ·
            refine ⟨1023721284101456347019029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364961712135275129358705 1023721284101456347019029)
            ·
              refine ⟨47986935192255766266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1023721284101456347019029 47986935192255766266517)
              ·
                refine ⟨2249387587136989043743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47986935192255766266517 2249387587136989043743)
                ·
                  rfl

theorem cell22_59139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 6].length) (baseStart_59139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59139 prefixEnd_59139 := by exact prefixLift 59139
  have htrace : WordTrace (prefixWord ++ tailWord_59139) baseStart_59139 baseEnd_59139 := by
    simpa [prefixWord, tailWord_59139, baseEnd_59139] using wordTrace_append hprefix tailTrace_59139
  have hstable : (prefixWord ++ tailWord_59139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59139).length < 2 ^ (prefixWord ++ tailWord_59139).sum := by decide
  have hdescent : baseEnd_59139 < baseStart_59139 := by decide
  rcases family_descends (prefixWord ++ tailWord_59139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59171 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 3, 3]
def baseStart_59171 : Nat := 118140960795 + 59171 * 2 ^ 59
def prefixEnd_59171 : Nat := 4983230072969 + 3 ^ 40 * 59171 * 2
def baseEnd_59171 : Nat := 20255442538195484593589

theorem tailTrace_59171 : CollatzResearch.WordTrace tailWord_59171 prefixEnd_59171 20255442538195484593589 := by
  unfold tailWord_59171
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158143668641047447361367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1438762445760698298240911 2158143668641047447361367)
  ·
    refine ⟨3237215502961571171042051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2158143668641047447361367 3237215502961571171042051)
    ·
      refine ⟨4855823254442356756563077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237215502961571171042051 4855823254442356756563077)
      ·
        refine ⟨910466860207941891855577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4855823254442356756563077 910466860207941891855577)
        ·
          refine ⟨682850145155956418891683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910466860207941891855577 682850145155956418891683)
          ·
            refine ⟨1024275217733934628337525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682850145155956418891683 1024275217733934628337525)
            ·
              refine ⟨96025801662556371406643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1024275217733934628337525 96025801662556371406643)
              ·
                refine ⟨144038702493834557109965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96025801662556371406643 144038702493834557109965)
                ·
                  refine ⟨54014513435187958916237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144038702493834557109965 54014513435187958916237)
                  ·
                    refine ⟨20255442538195484593589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54014513435187958916237 20255442538195484593589)
                    ·
                      rfl

theorem cell22_59171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].length) (baseStart_59171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59171 prefixEnd_59171 := by exact prefixLift 59171
  have htrace : WordTrace (prefixWord ++ tailWord_59171) baseStart_59171 baseEnd_59171 := by
    simpa [prefixWord, tailWord_59171, baseEnd_59171] using wordTrace_append hprefix tailTrace_59171
  have hstable : (prefixWord ++ tailWord_59171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59171).length < 2 ^ (prefixWord ++ tailWord_59171).sum := by decide
  have hdescent : baseEnd_59171 < baseStart_59171 := by decide
  rcases family_descends (prefixWord ++ tailWord_59171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59246 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_59246 : Nat := 118140960795 + 59246 * 2 ^ 59
def prefixEnd_59246 : Nat := 4983230072969 + 3 ^ 40 * 59246 * 2
def baseEnd_59246 : Nat := 6760372190306762989453

theorem tailTrace_59246 : CollatzResearch.WordTrace tailWord_59246 prefixEnd_59246 6760372190306762989453 := by
  unfold tailWord_59246
  simp only [CollatzResearch.WordTrace]
  refine ⟨270109892921166907042699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1440586095579556837561061 270109892921166907042699)
  ·
    refine ⟨405164839381750360564049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270109892921166907042699 405164839381750360564049)
    ·
      refine ⟨303873629536312770423037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405164839381750360564049 303873629536312770423037)
      ·
        refine ⟨113952611076117288908639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303873629536312770423037 113952611076117288908639)
        ·
          refine ⟨170928916614175933362959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113952611076117288908639 170928916614175933362959)
          ·
            refine ⟨256393374921263900044439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170928916614175933362959 256393374921263900044439)
            ·
              refine ⟨384590062381895850066659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256393374921263900044439 384590062381895850066659)
              ·
                refine ⟨576885093572843775099989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384590062381895850066659 576885093572843775099989)
                ·
                  refine ⟨6760372190306762989453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 576885093572843775099989 6760372190306762989453)
                  ·
                    rfl

theorem cell22_59246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_59246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59246 prefixEnd_59246 := by exact prefixLift 59246
  have htrace : WordTrace (prefixWord ++ tailWord_59246) baseStart_59246 baseEnd_59246 := by
    simpa [prefixWord, tailWord_59246, baseEnd_59246] using wordTrace_append hprefix tailTrace_59246
  have hstable : (prefixWord ++ tailWord_59246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59246).length < 2 ^ (prefixWord ++ tailWord_59246).sum := by decide
  have hdescent : baseEnd_59246 < baseStart_59246 := by decide
  rcases family_descends (prefixWord ++ tailWord_59246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59261 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_59261 : Nat := 118140960795 + 59261 * 2 ^ 59
def prefixEnd_59261 : Nat := 4983230072969 + 3 ^ 40 * 59261 * 2
def baseEnd_59261 : Nat := 20286251377465249843313

theorem tailTrace_59261 : CollatzResearch.WordTrace tailWord_59261 prefixEnd_59261 20286251377465249843313 := by
  unfold tailWord_59261
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161426238314992818137637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1440950825543328545425091 2161426238314992818137637)
  ·
    refine ⟨405267419684061153400807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2161426238314992818137637 405267419684061153400807)
    ·
      refine ⟨607901129526091730101211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405267419684061153400807 607901129526091730101211)
      ·
        refine ⟨911851694289137595151817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607901129526091730101211 911851694289137595151817)
        ·
          refine ⟨683888770716853196363863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911851694289137595151817 683888770716853196363863)
          ·
            refine ⟨1025833156075279794545795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683888770716853196363863 1025833156075279794545795)
            ·
              refine ⟨1538749734112919691818693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025833156075279794545795 1538749734112919691818693)
              ·
                refine ⟨288515575146172442216005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1538749734112919691818693 288515575146172442216005)
                ·
                  refine ⟨54096670339907332915501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288515575146172442216005 54096670339907332915501)
                  ·
                    refine ⟨20286251377465249843313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54096670339907332915501 20286251377465249843313)
                    ·
                      rfl

theorem cell22_59261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_59261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59261 prefixEnd_59261 := by exact prefixLift 59261
  have htrace : WordTrace (prefixWord ++ tailWord_59261) baseStart_59261 baseEnd_59261 := by
    simpa [prefixWord, tailWord_59261, baseEnd_59261] using wordTrace_append hprefix tailTrace_59261
  have hstable : (prefixWord ++ tailWord_59261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59261).length < 2 ^ (prefixWord ++ tailWord_59261).sum := by decide
  have hdescent : baseEnd_59261 < baseStart_59261 := by decide
  rcases family_descends (prefixWord ++ tailWord_59261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59265 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_59265 : Nat := 118140960795 + 59265 * 2 ^ 59
def prefixEnd_59265 : Nat := 4983230072969 + 3 ^ 40 * 59265 * 2
def baseEnd_59265 : Nat := 20287620659210572743301

theorem tailTrace_59265 : CollatzResearch.WordTrace tailWord_59265 prefixEnd_59265 20287620659210572743301 := by
  unfold tailWord_59265
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161572130300501501283249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1441048086867001000855499 2161572130300501501283249)
  ·
    refine ⟨1621179097725376125962437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2161572130300501501283249 1621179097725376125962437)
    ·
      refine ⟨303971080823508023617957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1621179097725376125962437 303971080823508023617957)
      ·
        refine ⟨56994577654407754428367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303971080823508023617957 56994577654407754428367)
        ·
          refine ⟨85491866481611631642551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56994577654407754428367 85491866481611631642551)
          ·
            refine ⟨128237799722417447463827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85491866481611631642551 128237799722417447463827)
            ·
              refine ⟨192356699583626171195741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128237799722417447463827 192356699583626171195741)
              ·
                refine ⟨72133762343859814198403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192356699583626171195741 72133762343859814198403)
                ·
                  refine ⟨108200643515789721297605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72133762343859814198403 108200643515789721297605)
                  ·
                    refine ⟨20287620659210572743301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108200643515789721297605 20287620659210572743301)
                    ·
                      rfl

theorem cell22_59265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_59265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59265 prefixEnd_59265 := by exact prefixLift 59265
  have htrace : WordTrace (prefixWord ++ tailWord_59265) baseStart_59265 baseEnd_59265 := by
    simpa [prefixWord, tailWord_59265, baseEnd_59265] using wordTrace_append hprefix tailTrace_59265
  have hstable : (prefixWord ++ tailWord_59265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59265).length < 2 ^ (prefixWord ++ tailWord_59265).sum := by decide
  have hdescent : baseEnd_59265 < baseStart_59265 := by decide
  rcases family_descends (prefixWord ++ tailWord_59265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59295 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 5]
def baseStart_59295 : Nat := 118140960795 + 59295 * 2 ^ 59
def prefixEnd_59295 : Nat := 4983230072969 + 3 ^ 40 * 59295 * 2
def baseEnd_59295 : Nat := 20297890272300494493209

theorem tailTrace_59295 : CollatzResearch.WordTrace tailWord_59295 prefixEnd_59295 20297890272300494493209 := by
  unfold tailWord_59295
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162666320191816624875339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1441777546794544416583559 2162666320191816624875339)
  ·
    refine ⟨3243999480287724937313009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162666320191816624875339 3243999480287724937313009)
    ·
      refine ⟨2432999610215793702984757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243999480287724937313009 2432999610215793702984757)
      ·
        refine ⟨228093713457730659654821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2432999610215793702984757 228093713457730659654821)
        ·
          refine ⟨42767571273324498685279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228093713457730659654821 42767571273324498685279)
          ·
            refine ⟨64151356909986748027919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42767571273324498685279 64151356909986748027919)
            ·
              refine ⟨96227035364980122041879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64151356909986748027919 96227035364980122041879)
              ·
                refine ⟨144340553047470183062819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96227035364980122041879 144340553047470183062819)
                ·
                  refine ⟨216510829571205274594229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144340553047470183062819 216510829571205274594229)
                  ·
                    refine ⟨20297890272300494493209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216510829571205274594229 20297890272300494493209)
                    ·
                      rfl

theorem cell22_59295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_59295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59295 prefixEnd_59295 := by exact prefixLift 59295
  have htrace : WordTrace (prefixWord ++ tailWord_59295) baseStart_59295 baseEnd_59295 := by
    simpa [prefixWord, tailWord_59295, baseEnd_59295] using wordTrace_append hprefix tailTrace_59295
  have hstable : (prefixWord ++ tailWord_59295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59295).length < 2 ^ (prefixWord ++ tailWord_59295).sum := by decide
  have hdescent : baseEnd_59295 < baseStart_59295 := by decide
  rcases family_descends (prefixWord ++ tailWord_59295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59336 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_59336 : Nat := 118140960795 + 59336 * 2 ^ 59
def prefixEnd_59336 : Nat := 4983230072969 + 3 ^ 40 * 59336 * 2
def baseEnd_59336 : Nat := 6770641803396684739361

theorem tailTrace_59336 : CollatzResearch.WordTrace tailWord_59336 prefixEnd_59336 6770641803396684739361 := by
  unfold tailWord_59336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082080856521640313558931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1442774475362187084745241 1082080856521640313558931)
  ·
    refine ⟨1623121284782460470338397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1082080856521640313558931 1623121284782460470338397)
    ·
      refine ⟨608670481793422676376899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1623121284782460470338397 608670481793422676376899)
      ·
        refine ⟨913005722690134014565349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608670481793422676376899 913005722690134014565349)
        ·
          refine ⟨171188573004400127731003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 913005722690134014565349 171188573004400127731003)
          ·
            refine ⟨256782859506600191596505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171188573004400127731003 256782859506600191596505)
            ·
              refine ⟨192587144629950143697379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256782859506600191596505 192587144629950143697379)
              ·
                refine ⟨288880716944925215546069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192587144629950143697379 288880716944925215546069)
                ·
                  refine ⟨6770641803396684739361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 288880716944925215546069 6770641803396684739361)
                  ·
                    rfl

theorem cell22_59336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_59336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59336 prefixEnd_59336 := by exact prefixLift 59336
  have htrace : WordTrace (prefixWord ++ tailWord_59336) baseStart_59336 baseEnd_59336 := by
    simpa [prefixWord, tailWord_59336, baseEnd_59336] using wordTrace_append hprefix tailTrace_59336
  have hstable : (prefixWord ++ tailWord_59336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59336).length < 2 ^ (prefixWord ++ tailWord_59336).sum := by decide
  have hdescent : baseEnd_59336 < baseStart_59336 := by decide
  rcases family_descends (prefixWord ++ tailWord_59336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59340 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_59340 : Nat := 118140960795 + 59340 * 2 ^ 59
def prefixEnd_59340 : Nat := 4983230072969 + 3 ^ 40 * 59340 * 2
def baseEnd_59340 : Nat := 20313294691935377118071

theorem tailTrace_59340 : CollatzResearch.WordTrace tailWord_59340 prefixEnd_59340 20313294691935377118071 := by
  unfold tailWord_59340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082153802514394655131737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1442871736685859540175649 1082153802514394655131737)
  ·
    refine ⟨811615351885795991348803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1082153802514394655131737 811615351885795991348803)
    ·
      refine ⟨1217423027828693987023205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811615351885795991348803 1217423027828693987023205)
      ·
        refine ⟨228266817717880122566851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1217423027828693987023205 228266817717880122566851)
        ·
          refine ⟨342400226576820183850277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228266817717880122566851 342400226576820183850277)
          ·
            refine ⟨64200042483153784471927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342400226576820183850277 64200042483153784471927)
            ·
              refine ⟨96300063724730676707891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64200042483153784471927 96300063724730676707891)
              ·
                refine ⟨144450095587096015061837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96300063724730676707891 144450095587096015061837)
                ·
                  refine ⟨54168785845161005648189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144450095587096015061837 54168785845161005648189)
                  ·
                    refine ⟨20313294691935377118071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54168785845161005648189 20313294691935377118071)
                    ·
                      rfl

theorem cell22_59340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_59340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59340 prefixEnd_59340 := by exact prefixLift 59340
  have htrace : WordTrace (prefixWord ++ tailWord_59340) baseStart_59340 baseEnd_59340 := by
    simpa [prefixWord, tailWord_59340, baseEnd_59340] using wordTrace_append hprefix tailTrace_59340
  have hstable : (prefixWord ++ tailWord_59340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59340).length < 2 ^ (prefixWord ++ tailWord_59340).sum := by decide
  have hdescent : baseEnd_59340 < baseStart_59340 := by decide
  rcases family_descends (prefixWord ++ tailWord_59340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59353 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 5]
def baseStart_59353 : Nat := 118140960795 + 59353 * 2 ^ 59
def prefixEnd_59353 : Nat := 4983230072969 + 3 ^ 40 * 59353 * 2
def baseEnd_59353 : Nat := 6772581619202558847677

theorem tailTrace_59353 : CollatzResearch.WordTrace tailWord_59353 prefixEnd_59353 6772581619202558847677 := by
  unfold tailWord_59353
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164781753981692530486713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1443187835987795020324475 2164781753981692530486713)
  ·
    refine ⟨1623586315486269397865035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2164781753981692530486713 1623586315486269397865035)
    ·
      refine ⟨2435379473229404096797553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623586315486269397865035 2435379473229404096797553)
      ·
        refine ⟨1826534604922053072598165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435379473229404096797553 1826534604922053072598165)
        ·
          refine ⟨85618809605721237778039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1826534604922053072598165 85618809605721237778039)
          ·
            refine ⟨128428214408581856667059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85618809605721237778039 128428214408581856667059)
            ·
              refine ⟨192642321612872785000589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128428214408581856667059 192642321612872785000589)
              ·
                refine ⟨72240870604827294375221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192642321612872785000589 72240870604827294375221)
                ·
                  refine ⟨6772581619202558847677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72240870604827294375221 6772581619202558847677)
                  ·
                    rfl

theorem cell22_59353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_59353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59353 prefixEnd_59353 := by exact prefixLift 59353
  have htrace : WordTrace (prefixWord ++ tailWord_59353) baseStart_59353 baseEnd_59353 := by
    simpa [prefixWord, tailWord_59353, baseEnd_59353] using wordTrace_append hprefix tailTrace_59353
  have hstable : (prefixWord ++ tailWord_59353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59353).length < 2 ^ (prefixWord ++ tailWord_59353).sum := by decide
  have hdescent : baseEnd_59353 < baseStart_59353 := by decide
  rcases family_descends (prefixWord ++ tailWord_59353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59411 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_59411 : Nat := 118140960795 + 59411 * 2 ^ 59
def prefixEnd_59411 : Nat := 4983230072969 + 3 ^ 40 * 59411 * 2
def baseEnd_59411 : Nat := 20337599442914858592853

theorem tailTrace_59411 : CollatzResearch.WordTrace tailWord_59411 prefixEnd_59411 20337599442914858592853 := by
  unfold tailWord_59411
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166897187771568436098087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1444598125181045624065391 2166897187771568436098087)
  ·
    refine ⟨3250345781657352654147131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166897187771568436098087 3250345781657352654147131)
    ·
      refine ⟨4875518672486028981220697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250345781657352654147131 4875518672486028981220697)
      ·
        refine ⟨3656639004364521735915523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875518672486028981220697 3656639004364521735915523)
        ·
          refine ⟨5484958506546782603873285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656639004364521735915523 5484958506546782603873285)
          ·
            refine ⟨1028429719977521738226241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5484958506546782603873285 1028429719977521738226241)
            ·
              refine ⟨771322289983141303669681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028429719977521738226241 771322289983141303669681)
              ·
                refine ⟨578491717487355977752261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771322289983141303669681 578491717487355977752261)
                ·
                  refine ⟨108467197028879245828549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578491717487355977752261 108467197028879245828549)
                  ·
                    refine ⟨20337599442914858592853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108467197028879245828549 20337599442914858592853)
                    ·
                      rfl

theorem cell22_59411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_59411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59411 prefixEnd_59411 := by exact prefixLift 59411
  have htrace : WordTrace (prefixWord ++ tailWord_59411) baseStart_59411 baseEnd_59411 := by
    simpa [prefixWord, tailWord_59411, baseEnd_59411] using wordTrace_append hprefix tailTrace_59411
  have hstable : (prefixWord ++ tailWord_59411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59411).length < 2 ^ (prefixWord ++ tailWord_59411).sum := by decide
  have hdescent : baseEnd_59411 < baseStart_59411 := by decide
  rcases family_descends (prefixWord ++ tailWord_59411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59492 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_59492 : Nat := 118140960795 + 59492 * 2 ^ 59
def prefixEnd_59492 : Nat := 4983230072969 + 3 ^ 40 * 59492 * 2
def baseEnd_59492 : Nat := 20365327398257647317605

theorem tailTrace_59492 : CollatzResearch.WordTrace tailWord_59492 prefixEnd_59492 20365327398257647317605 := by
  unfold tailWord_59492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084925750239059634898365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1446567666985412846531153 1084925750239059634898365)
  ·
    refine ⟨406847156339647363086887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1084925750239059634898365 406847156339647363086887)
    ·
      refine ⟨610270734509471044630331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406847156339647363086887 610270734509471044630331)
      ·
        refine ⟨915406101764206566945497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610270734509471044630331 915406101764206566945497)
        ·
          refine ⟨686554576323154925209123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915406101764206566945497 686554576323154925209123)
          ·
            refine ⟨1029831864484732387813685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686554576323154925209123 1029831864484732387813685)
            ·
              refine ⟨96546737295443661357533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1029831864484732387813685 96546737295443661357533)
              ·
                refine ⟨36205026485791373009075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96546737295443661357533 36205026485791373009075)
                ·
                  refine ⟨54307539728687059513613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36205026485791373009075 54307539728687059513613)
                  ·
                    refine ⟨20365327398257647317605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54307539728687059513613 20365327398257647317605)
                    ·
                      rfl

theorem cell22_59492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_59492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59492 prefixEnd_59492 := by exact prefixLift 59492
  have htrace : WordTrace (prefixWord ++ tailWord_59492) baseStart_59492 baseEnd_59492 := by
    simpa [prefixWord, tailWord_59492, baseEnd_59492] using wordTrace_append hprefix tailTrace_59492
  have hstable : (prefixWord ++ tailWord_59492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59492).length < 2 ^ (prefixWord ++ tailWord_59492).sum := by decide
  have hdescent : baseEnd_59492 < baseStart_59492 := by decide
  rcases family_descends (prefixWord ++ tailWord_59492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59552 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_59552 : Nat := 118140960795 + 59552 * 2 ^ 59
def prefixEnd_59552 : Nat := 4983230072969 + 3 ^ 40 * 59552 * 2
def baseEnd_59552 : Nat := 20385866624437490817421

theorem tailTrace_59552 : CollatzResearch.WordTrace tailWord_59552 prefixEnd_59552 20385866624437490817421 := by
  unfold tailWord_59552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086019940130374758490455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1448026586840499677987273 1086019940130374758490455)
  ·
    refine ⟨1629029910195562137735683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086019940130374758490455 1629029910195562137735683)
    ·
      refine ⟨2443544865293343206603525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629029910195562137735683 2443544865293343206603525)
      ·
        refine ⟨458164662242501851238161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2443544865293343206603525 458164662242501851238161)
        ·
          refine ⟨343623496681876388428621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458164662242501851238161 343623496681876388428621)
          ·
            refine ⟨128858811255703645660733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343623496681876388428621 128858811255703645660733)
            ·
              refine ⟨48322054220888867122775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128858811255703645660733 48322054220888867122775)
              ·
                refine ⟨72483081331333300684163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48322054220888867122775 72483081331333300684163)
                ·
                  refine ⟨108724621996999951026245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72483081331333300684163 108724621996999951026245)
                  ·
                    refine ⟨20385866624437490817421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108724621996999951026245 20385866624437490817421)
                    ·
                      rfl

theorem cell22_59552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_59552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59552 prefixEnd_59552 := by exact prefixLift 59552
  have htrace : WordTrace (prefixWord ++ tailWord_59552) baseStart_59552 baseEnd_59552 := by
    simpa [prefixWord, tailWord_59552, baseEnd_59552] using wordTrace_append hprefix tailTrace_59552
  have hstable : (prefixWord ++ tailWord_59552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59552).length < 2 ^ (prefixWord ++ tailWord_59552).sum := by decide
  have hdescent : baseEnd_59552 < baseStart_59552 := by decide
  rcases family_descends (prefixWord ++ tailWord_59552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59578 : List Nat := [3, 1, 1, 1, 2, 2, 5, 7]
def baseStart_59578 : Nat := 118140960795 + 59578 * 2 ^ 59
def prefixEnd_59578 : Nat := 4983230072969 + 3 ^ 40 * 59578 * 2
def baseEnd_59578 : Nat := 2266085217309121074149

theorem tailTrace_59578 : CollatzResearch.WordTrace tailWord_59578 prefixEnd_59578 2266085217309121074149 := by
  unfold tailWord_59578
  simp only [CollatzResearch.WordTrace]
  refine ⟨543247044541638989356847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1448658785444370638284925 543247044541638989356847)
  ·
    refine ⟨814870566812458484035271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543247044541638989356847 814870566812458484035271)
    ·
      refine ⟨1222305850218687726052907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814870566812458484035271 1222305850218687726052907)
      ·
        refine ⟨1833458775328031589079361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222305850218687726052907 1833458775328031589079361)
        ·
          refine ⟨1375094081496023691809521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1833458775328031589079361 1375094081496023691809521)
          ·
            refine ⟨1031320561122017768857141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375094081496023691809521 1031320561122017768857141)
            ·
              refine ⟨96686302605189165830357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1031320561122017768857141 96686302605189165830357)
              ·
                refine ⟨2266085217309121074149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96686302605189165830357 2266085217309121074149)
                ·
                  rfl

theorem cell22_59578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_59578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59578 prefixEnd_59578 := by exact prefixLift 59578
  have htrace : WordTrace (prefixWord ++ tailWord_59578) baseStart_59578 baseEnd_59578 := by
    simpa [prefixWord, tailWord_59578, baseEnd_59578] using wordTrace_append hprefix tailTrace_59578
  have hstable : (prefixWord ++ tailWord_59578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59578).length < 2 ^ (prefixWord ++ tailWord_59578).sum := by decide
  have hdescent : baseEnd_59578 < baseStart_59578 := by decide
  rcases family_descends (prefixWord ++ tailWord_59578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59582 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_59582 : Nat := 118140960795 + 59582 * 2 ^ 59
def prefixEnd_59582 : Nat := 4983230072969 + 3 ^ 40 * 59582 * 2
def baseEnd_59582 : Nat := 20396136237527412567329

theorem tailTrace_59582 : CollatzResearch.WordTrace tailWord_59582 prefixEnd_59582 20396136237527412567329 := by
  unfold tailWord_59582
  simp only [CollatzResearch.WordTrace]
  refine ⟨271641758769008080071625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1448756046768043093715333 271641758769008080071625)
  ·
    refine ⟨203731319076756060053719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271641758769008080071625 203731319076756060053719)
    ·
      refine ⟨305596978615134090080579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203731319076756060053719 305596978615134090080579)
      ·
        refine ⟨458395467922701135120869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305596978615134090080579 458395467922701135120869)
        ·
          refine ⟨85949150235506462835163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458395467922701135120869 85949150235506462835163)
          ·
            refine ⟨128923725353259694252745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85949150235506462835163 128923725353259694252745)
            ·
              refine ⟨96692794014944770689559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128923725353259694252745 96692794014944770689559)
              ·
                refine ⟨145039191022417156034339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96692794014944770689559 145039191022417156034339)
                ·
                  refine ⟨217558786533625734051509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145039191022417156034339 217558786533625734051509)
                  ·
                    refine ⟨20396136237527412567329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217558786533625734051509 20396136237527412567329)
                    ·
                      rfl

theorem cell22_59582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_59582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59582 prefixEnd_59582 := by exact prefixLift 59582
  have htrace : WordTrace (prefixWord ++ tailWord_59582) baseStart_59582 baseEnd_59582 := by
    simpa [prefixWord, tailWord_59582, baseEnd_59582] using wordTrace_append hprefix tailTrace_59582
  have hstable : (prefixWord ++ tailWord_59582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59582).length < 2 ^ (prefixWord ++ tailWord_59582).sum := by decide
  have hdescent : baseEnd_59582 < baseStart_59582 := by decide
  rcases family_descends (prefixWord ++ tailWord_59582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59612 : List Nat := [2, 2, 5, 2, 1, 1, 9]
def baseStart_59612 : Nat := 118140960795 + 59612 * 2 ^ 59
def prefixEnd_59612 : Nat := 4983230072969 + 3 ^ 40 * 59612 * 2
def baseEnd_59612 : Nat := 755792809282123493231

theorem tailTrace_59612 : CollatzResearch.WordTrace tailWord_59612 prefixEnd_59612 755792809282123493231 := by
  unfold tailWord_59612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087114130021689882082545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1449485506695586509443393 1087114130021689882082545)
  ·
    refine ⟨815335597516267411561909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087114130021689882082545 815335597516267411561909)
    ·
      refine ⟨76437712267150069833929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 815335597516267411561909 76437712267150069833929)
      ·
        refine ⟨57328284200362552375447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76437712267150069833929 57328284200362552375447)
        ·
          refine ⟨85992426300543828563171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57328284200362552375447 85992426300543828563171)
          ·
            refine ⟨128988639450815742844757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85992426300543828563171 128988639450815742844757)
            ·
              refine ⟨755792809282123493231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 128988639450815742844757 755792809282123493231)
              ·
                rfl

theorem cell22_59612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 9].length) (baseStart_59612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59612 prefixEnd_59612 := by exact prefixLift 59612
  have htrace : WordTrace (prefixWord ++ tailWord_59612) baseStart_59612 baseEnd_59612 := by
    simpa [prefixWord, tailWord_59612, baseEnd_59612] using wordTrace_append hprefix tailTrace_59612
  have hstable : (prefixWord ++ tailWord_59612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59612).length < 2 ^ (prefixWord ++ tailWord_59612).sum := by decide
  have hdescent : baseEnd_59612 < baseStart_59612 := by decide
  rcases family_descends (prefixWord ++ tailWord_59612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59627 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 1, 3]
def baseStart_59627 : Nat := 118140960795 + 59627 * 2 ^ 59
def prefixEnd_59627 : Nat := 4983230072969 + 3 ^ 40 * 59627 * 2
def baseEnd_59627 : Nat := 20411540657162295192191

theorem tailTrace_59627 : CollatzResearch.WordTrace tailWord_59627 prefixEnd_59627 20411540657162295192191 := by
  unfold tailWord_59627
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174775354989037325961135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1449850236659358217307423 2174775354989037325961135)
  ·
    refine ⟨3262163032483555988941703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174775354989037325961135 3262163032483555988941703)
    ·
      refine ⟨4893244548725333983412555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262163032483555988941703 4893244548725333983412555)
      ·
        refine ⟨7339866823088000975118833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893244548725333983412555 7339866823088000975118833)
        ·
          refine ⟨5504900117316000731339125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7339866823088000975118833 5504900117316000731339125)
          ·
            refine ⟨516084385998375068563043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5504900117316000731339125 516084385998375068563043)
            ·
              refine ⟨774126578997562602844565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516084385998375068563043 774126578997562602844565)
              ·
                refine ⟨36287183390510747008339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 774126578997562602844565 36287183390510747008339)
                ·
                  refine ⟨54430775085766120512509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36287183390510747008339 54430775085766120512509)
                  ·
                    refine ⟨20411540657162295192191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54430775085766120512509 20411540657162295192191)
                    ·
                      rfl

theorem cell22_59627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 3].length) (baseStart_59627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59627 prefixEnd_59627 := by exact prefixLift 59627
  have htrace : WordTrace (prefixWord ++ tailWord_59627) baseStart_59627 baseEnd_59627 := by
    simpa [prefixWord, tailWord_59627, baseEnd_59627] using wordTrace_append hprefix tailTrace_59627
  have hstable : (prefixWord ++ tailWord_59627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59627).length < 2 ^ (prefixWord ++ tailWord_59627).sum := by decide
  have hdescent : baseEnd_59627 < baseStart_59627 := by decide
  rcases family_descends (prefixWord ++ tailWord_59627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59715 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_59715 : Nat := 118140960795 + 59715 * 2 ^ 59
def prefixEnd_59715 : Nat := 4983230072969 + 3 ^ 40 * 59715 * 2
def baseEnd_59715 : Nat := 20441664855559398991921

theorem tailTrace_59715 : CollatzResearch.WordTrace tailWord_59715 prefixEnd_59715 20441664855559398991921 := by
  unfold tailWord_59715
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177984978670228355164599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1451989985780152236776399 2177984978670228355164599)
  ·
    refine ⟨3266977468005342532746899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177984978670228355164599 3266977468005342532746899)
    ·
      refine ⟨4900466202008013799120349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266977468005342532746899 4900466202008013799120349)
      ·
        refine ⟨1837674825753005174670131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4900466202008013799120349 1837674825753005174670131)
        ·
          refine ⟨2756512238629507762005197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837674825753005174670131 2756512238629507762005197)
          ·
            refine ⟨1033692089486065410751949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2756512238629507762005197 1033692089486065410751949)
            ·
              refine ⟨387634533557274529031981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033692089486065410751949 387634533557274529031981)
              ·
                refine ⟨145362950083977948386993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387634533557274529031981 145362950083977948386993)
                ·
                  refine ⟨109022212562983461290245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145362950083977948386993 109022212562983461290245)
                  ·
                    refine ⟨20441664855559398991921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109022212562983461290245 20441664855559398991921)
                    ·
                      rfl

theorem cell22_59715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_59715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59715 prefixEnd_59715 := by exact prefixLift 59715
  have htrace : WordTrace (prefixWord ++ tailWord_59715) baseStart_59715 baseEnd_59715 := by
    simpa [prefixWord, tailWord_59715, baseEnd_59715] using wordTrace_append hprefix tailTrace_59715
  have hstable : (prefixWord ++ tailWord_59715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59715).length < 2 ^ (prefixWord ++ tailWord_59715).sum := by decide
  have hdescent : baseEnd_59715 < baseStart_59715 := by decide
  rcases family_descends (prefixWord ++ tailWord_59715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59732 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_59732 : Nat := 118140960795 + 59732 * 2 ^ 59
def prefixEnd_59732 : Nat := 4983230072969 + 3 ^ 40 * 59732 * 2
def baseEnd_59732 : Nat := 20447484302977021316869

theorem tailTrace_59732 : CollatzResearch.WordTrace tailWord_59732 prefixEnd_59732 20447484302977021316869 := by
  unfold tailWord_59732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089302509804320129266725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1452403346405760172355633 1089302509804320129266725)
  ·
    refine ⟨204244220588310024237511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1089302509804320129266725 204244220588310024237511)
    ·
      refine ⟨306366330882465036356267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204244220588310024237511 306366330882465036356267)
      ·
        refine ⟨459549496323697554534401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306366330882465036356267 459549496323697554534401)
        ·
          refine ⟨344662122242773165900801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459549496323697554534401 344662122242773165900801)
          ·
            refine ⟨258496591682079874425601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344662122242773165900801 258496591682079874425601)
            ·
              refine ⟨193872443761559905819201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258496591682079874425601 193872443761559905819201)
              ·
                refine ⟨145404332821169929364401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193872443761559905819201 145404332821169929364401)
                ·
                  refine ⟨109053249615877447023301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145404332821169929364401 109053249615877447023301)
                  ·
                    refine ⟨20447484302977021316869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109053249615877447023301 20447484302977021316869)
                    ·
                      rfl

theorem cell22_59732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_59732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59732 prefixEnd_59732 := by exact prefixLift 59732
  have htrace : WordTrace (prefixWord ++ tailWord_59732) baseStart_59732 baseEnd_59732 := by
    simpa [prefixWord, tailWord_59732, baseEnd_59732] using wordTrace_append hprefix tailTrace_59732
  have hstable : (prefixWord ++ tailWord_59732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59732).length < 2 ^ (prefixWord ++ tailWord_59732).sum := by decide
  have hdescent : baseEnd_59732 < baseStart_59732 := by decide
  rcases family_descends (prefixWord ++ tailWord_59732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59762 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_59762 : Nat := 118140960795 + 59762 * 2 ^ 59
def prefixEnd_59762 : Nat := 4983230072969 + 3 ^ 40 * 59762 * 2
def baseEnd_59762 : Nat := 20457753916066943066777

theorem tailTrace_59762 : CollatzResearch.WordTrace tailWord_59762 prefixEnd_59762 20457753916066943066777 := by
  unfold tailWord_59762
  simp only [CollatzResearch.WordTrace]
  refine ⟨544924802374988845531385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1453132806333303588083693 544924802374988845531385)
  ·
    refine ⟨408693601781241634148539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 544924802374988845531385 408693601781241634148539)
    ·
      refine ⟨613040402671862451222809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408693601781241634148539 613040402671862451222809)
      ·
        refine ⟨459780302003896838417107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613040402671862451222809 459780302003896838417107)
        ·
          refine ⟨689670453005845257625661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459780302003896838417107 689670453005845257625661)
          ·
            refine ⟨258626419877191971609623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689670453005845257625661 258626419877191971609623)
            ·
              refine ⟨387939629815787957414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258626419877191971609623 387939629815787957414435)
              ·
                refine ⟨581909444723681936121653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387939629815787957414435 581909444723681936121653)
                ·
                  refine ⟨54554010442845181511405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581909444723681936121653 54554010442845181511405)
                  ·
                    refine ⟨20457753916066943066777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54554010442845181511405 20457753916066943066777)
                    ·
                      rfl

theorem cell22_59762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_59762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59762 prefixEnd_59762 := by exact prefixLift 59762
  have htrace : WordTrace (prefixWord ++ tailWord_59762) baseStart_59762 baseEnd_59762 := by
    simpa [prefixWord, tailWord_59762, baseEnd_59762] using wordTrace_append hprefix tailTrace_59762
  have hstable : (prefixWord ++ tailWord_59762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59762).length < 2 ^ (prefixWord ++ tailWord_59762).sum := by decide
  have hdescent : baseEnd_59762 < baseStart_59762 := by decide
  rcases family_descends (prefixWord ++ tailWord_59762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59796 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_59796 : Nat := 118140960795 + 59796 * 2 ^ 59
def prefixEnd_59796 : Nat := 4983230072969 + 3 ^ 40 * 59796 * 2
def baseEnd_59796 : Nat := 20469392810902187716673

theorem tailTrace_59796 : CollatzResearch.WordTrace tailWord_59796 prefixEnd_59796 20469392810902187716673 := by
  unfold tailWord_59796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090469645688389594431621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1453959527584519459242161 1090469645688389594431621)
  ·
    refine ⟨204463058566573048955929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1090469645688389594431621 204463058566573048955929)
    ·
      refine ⟨153347293924929786716947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204463058566573048955929 153347293924929786716947)
      ·
        refine ⟨230020940887394680075421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153347293924929786716947 230020940887394680075421)
        ·
          refine ⟨86257852832773005028283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230020940887394680075421 86257852832773005028283)
          ·
            refine ⟨129386779249159507542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86257852832773005028283 129386779249159507542425)
            ·
              refine ⟨97040084436869630656819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129386779249159507542425 97040084436869630656819)
              ·
                refine ⟨145560126655304445985229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97040084436869630656819 145560126655304445985229)
                ·
                  refine ⟨54585047495739167244461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145560126655304445985229 54585047495739167244461)
                  ·
                    refine ⟨20469392810902187716673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54585047495739167244461 20469392810902187716673)
                    ·
                      rfl

theorem cell22_59796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_59796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59796 prefixEnd_59796 := by exact prefixLift 59796
  have htrace : WordTrace (prefixWord ++ tailWord_59796) baseStart_59796 baseEnd_59796 := by
    simpa [prefixWord, tailWord_59796, baseEnd_59796] using wordTrace_append hprefix tailTrace_59796
  have hstable : (prefixWord ++ tailWord_59796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59796).length < 2 ^ (prefixWord ++ tailWord_59796).sum := by decide
  have hdescent : baseEnd_59796 < baseStart_59796 := by decide
  rcases family_descends (prefixWord ++ tailWord_59796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59882 : List Nat := [3, 1, 3, 1, 3, 1, 2, 8]
def baseStart_59882 : Nat := 118140960795 + 59882 * 2 ^ 59
def prefixEnd_59882 : Nat := 4983230072969 + 3 ^ 40 * 59882 * 2
def baseEnd_59882 : Nat := 2277648040936292229601

theorem tailTrace_59882 : CollatzResearch.WordTrace tailWord_59882 prefixEnd_59882 2277648040936292229601 := by
  unfold tailWord_59882
  simp only [CollatzResearch.WordTrace]
  refine ⟨546018992266303969123475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1456050646043477250995933 546018992266303969123475)
  ·
    refine ⟨819028488399455953685213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546018992266303969123475 819028488399455953685213)
    ·
      refine ⟨307135683149795982631955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 819028488399455953685213 307135683149795982631955)
      ·
        refine ⟨460703524724693973947933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307135683149795982631955 460703524724693973947933)
        ·
          refine ⟨172763821771760240230475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460703524724693973947933 172763821771760240230475)
          ·
            refine ⟨259145732657640360345713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172763821771760240230475 259145732657640360345713)
            ·
              refine ⟨194359299493230270259285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259145732657640360345713 194359299493230270259285)
              ·
                refine ⟨2277648040936292229601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194359299493230270259285 2277648040936292229601)
                ·
                  rfl

theorem cell22_59882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_59882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59882 prefixEnd_59882 := by exact prefixLift 59882
  have htrace : WordTrace (prefixWord ++ tailWord_59882) baseStart_59882 baseEnd_59882 := by
    simpa [prefixWord, tailWord_59882, baseEnd_59882] using wordTrace_append hprefix tailTrace_59882
  have hstable : (prefixWord ++ tailWord_59882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59882).length < 2 ^ (prefixWord ++ tailWord_59882).sum := by decide
  have hdescent : baseEnd_59882 < baseStart_59882 := by decide
  rcases family_descends (prefixWord ++ tailWord_59882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59914 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_59914 : Nat := 118140960795 + 59914 * 2 ^ 59
def prefixEnd_59914 : Nat := 4983230072969 + 3 ^ 40 * 59914 * 2
def baseEnd_59914 : Nat := 20509786622389213266311

theorem tailTrace_59914 : CollatzResearch.WordTrace tailWord_59914 prefixEnd_59914 20509786622389213266311 := by
  unfold tailWord_59914
  simp only [CollatzResearch.WordTrace]
  refine ⟨546310776237321335414699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1456828736632856894439197 546310776237321335414699)
  ·
    refine ⟨819466164355982003122049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546310776237321335414699 819466164355982003122049)
    ·
      refine ⟨614599623266986502341537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 819466164355982003122049 614599623266986502341537)
      ·
        refine ⟨460949717450239876756153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614599623266986502341537 460949717450239876756153)
        ·
          refine ⟨345712288087679907567115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460949717450239876756153 345712288087679907567115)
          ·
            refine ⟨518568432131519861350673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345712288087679907567115 518568432131519861350673)
            ·
              refine ⟨388926324098639896013005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518568432131519861350673 388926324098639896013005)
              ·
                refine ⟨145847371536989961004877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388926324098639896013005 145847371536989961004877)
                ·
                  refine ⟨54692764326371235376829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145847371536989961004877 54692764326371235376829)
                  ·
                    refine ⟨20509786622389213266311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54692764326371235376829 20509786622389213266311)
                    ·
                      rfl

theorem cell22_59914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_59914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_59914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_59914 prefixEnd_59914 := by exact prefixLift 59914
  have htrace : WordTrace (prefixWord ++ tailWord_59914) baseStart_59914 baseEnd_59914 := by
    simpa [prefixWord, tailWord_59914, baseEnd_59914] using wordTrace_append hprefix tailTrace_59914
  have hstable : (prefixWord ++ tailWord_59914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59914).length < 2 ^ (prefixWord ++ tailWord_59914).sum := by decide
  have hdescent : baseEnd_59914 < baseStart_59914 := by decide
  rcases family_descends (prefixWord ++ tailWord_59914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60004 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_60004 : Nat := 118140960795 + 60004 * 2 ^ 59
def prefixEnd_60004 : Nat := 4983230072969 + 3 ^ 40 * 60004 * 2
def baseEnd_60004 : Nat := 20540595461658978516035

theorem tailTrace_60004 : CollatzResearch.WordTrace tailWord_60004 prefixEnd_60004 20540595461658978516035 := by
  unfold tailWord_60004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094262837311615356217533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1459017116415487141623377 1094262837311615356217533)
  ·
    refine ⟨410348563991855758581575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1094262837311615356217533 410348563991855758581575)
    ·
      refine ⟨615522845987783637872363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410348563991855758581575 615522845987783637872363)
      ·
        refine ⟨923284268981675456808545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615522845987783637872363 923284268981675456808545)
        ·
          refine ⟨692463201736256592606409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923284268981675456808545 692463201736256592606409)
          ·
            refine ⟨519347401302192444454807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692463201736256592606409 519347401302192444454807)
            ·
              refine ⟨779021101953288666682211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519347401302192444454807 779021101953288666682211)
              ·
                refine ⟨1168531652929933000023317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779021101953288666682211 1168531652929933000023317)
                ·
                  refine ⟨54774921231090609376093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1168531652929933000023317 54774921231090609376093)
                  ·
                    refine ⟨20540595461658978516035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54774921231090609376093 20540595461658978516035)
                    ·
                      rfl

theorem cell22_60004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_60004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60004 prefixEnd_60004 := by exact prefixLift 60004
  have htrace : WordTrace (prefixWord ++ tailWord_60004) baseStart_60004 baseEnd_60004 := by
    simpa [prefixWord, tailWord_60004, baseEnd_60004] using wordTrace_append hprefix tailTrace_60004
  have hstable : (prefixWord ++ tailWord_60004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60004).length < 2 ^ (prefixWord ++ tailWord_60004).sum := by decide
  have hdescent : baseEnd_60004 < baseStart_60004 := by decide
  rcases family_descends (prefixWord ++ tailWord_60004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60047 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_60047 : Nat := 118140960795 + 60047 * 2 ^ 59
def prefixEnd_60047 : Nat := 4983230072969 + 3 ^ 40 * 60047 * 2
def baseEnd_60047 : Nat := 20555315240421199690903

theorem tailTrace_60047 : CollatzResearch.WordTrace tailWord_60047 prefixEnd_60047 20555315240421199690903 := by
  unfold tailWord_60047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190094013467449056250395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460062675644966037500263 2190094013467449056250395)
  ·
    refine ⟨3285141020201173584375593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190094013467449056250395 3285141020201173584375593)
    ·
      refine ⟨2463855765150880188281695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285141020201173584375593 2463855765150880188281695)
      ·
        refine ⟨3695783647726320282422543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463855765150880188281695 3695783647726320282422543)
        ·
          refine ⟨5543675471589480423633815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695783647726320282422543 5543675471589480423633815)
          ·
            refine ⟨8315513207384220635450723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543675471589480423633815 8315513207384220635450723)
            ·
              refine ⟨12473269811076330953176085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315513207384220635450723 12473269811076330953176085)
              ·
                refine ⟨584684522394203013430129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12473269811076330953176085 584684522394203013430129)
                ·
                  refine ⟨438513391795652260072597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584684522394203013430129 438513391795652260072597)
                  ·
                    refine ⟨20555315240421199690903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 438513391795652260072597 20555315240421199690903)
                    ·
                      rfl

theorem cell22_60047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_60047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60047 prefixEnd_60047 := by exact prefixLift 60047
  have htrace : WordTrace (prefixWord ++ tailWord_60047) baseStart_60047 baseEnd_60047 := by
    simpa [prefixWord, tailWord_60047, baseEnd_60047] using wordTrace_append hprefix tailTrace_60047
  have hstable : (prefixWord ++ tailWord_60047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60047).length < 2 ^ (prefixWord ++ tailWord_60047).sum := by decide
  have hdescent : baseEnd_60047 < baseStart_60047 := by decide
  rcases family_descends (prefixWord ++ tailWord_60047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60074 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_60074 : Nat := 118140960795 + 60074 * 2 ^ 59
def prefixEnd_60074 : Nat := 4983230072969 + 3 ^ 40 * 60074 * 2
def baseEnd_60074 : Nat := 6854852630734043088607

theorem tailTrace_60074 : CollatzResearch.WordTrace tailWord_60074 prefixEnd_60074 6854852630734043088607 := by
  unfold tailWord_60074
  simp only [CollatzResearch.WordTrace]
  refine ⟨547769696092408166870819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1460719189579755111655517 547769696092408166870819)
  ·
    refine ⟨821654544138612250306229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547769696092408166870819 821654544138612250306229)
    ·
      refine ⟨77030113512994898466209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 821654544138612250306229 77030113512994898466209)
      ·
        refine ⟨57772585134746173849657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77030113512994898466209 57772585134746173849657)
        ·
          refine ⟨43329438851059630387243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57772585134746173849657 43329438851059630387243)
          ·
            refine ⟨64994158276589445580865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43329438851059630387243 64994158276589445580865)
            ·
              refine ⟨48745618707442084185649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64994158276589445580865 48745618707442084185649)
              ·
                refine ⟨36559214030581563139237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48745618707442084185649 36559214030581563139237)
                ·
                  refine ⟨6854852630734043088607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36559214030581563139237 6854852630734043088607)
                  ·
                    rfl

theorem cell22_60074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_60074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60074 prefixEnd_60074 := by exact prefixLift 60074
  have htrace : WordTrace (prefixWord ++ tailWord_60074) baseStart_60074 baseEnd_60074 := by
    simpa [prefixWord, tailWord_60074, baseEnd_60074] using wordTrace_append hprefix tailTrace_60074
  have hstable : (prefixWord ++ tailWord_60074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60074).length < 2 ^ (prefixWord ++ tailWord_60074).sum := by decide
  have hdescent : baseEnd_60074 < baseStart_60074 := by decide
  rcases family_descends (prefixWord ++ tailWord_60074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60079 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 5]
def baseStart_60079 : Nat := 118140960795 + 60079 * 2 ^ 59
def prefixEnd_60079 : Nat := 4983230072969 + 3 ^ 40 * 60079 * 2
def baseEnd_60079 : Nat := 6855423164794594296935

theorem tailTrace_60079 : CollatzResearch.WordTrace tailWord_60079 prefixEnd_60079 6855423164794594296935 := by
  unfold tailWord_60079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191261149351518521415291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460840766234345680943527 2191261149351518521415291)
  ·
    refine ⟨3286891724027277782122937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191261149351518521415291 3286891724027277782122937)
    ·
      refine ⟨2465168793020458336592203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286891724027277782122937 2465168793020458336592203)
      ·
        refine ⟨3697753189530687504888305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465168793020458336592203 3697753189530687504888305)
        ·
          refine ⟨2773314892148015628666229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697753189530687504888305 2773314892148015628666229)
          ·
            refine ⟨259998271138876465187459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2773314892148015628666229 259998271138876465187459)
            ·
              refine ⟨389997406708314697781189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259998271138876465187459 389997406708314697781189)
              ·
                refine ⟨73124513757809005833973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389997406708314697781189 73124513757809005833973)
                ·
                  refine ⟨6855423164794594296935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73124513757809005833973 6855423164794594296935)
                  ·
                    rfl

theorem cell22_60079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].length) (baseStart_60079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60079 prefixEnd_60079 := by exact prefixLift 60079
  have htrace : WordTrace (prefixWord ++ tailWord_60079) baseStart_60079 baseEnd_60079 := by
    simpa [prefixWord, tailWord_60079, baseEnd_60079] using wordTrace_append hprefix tailTrace_60079
  have hstable : (prefixWord ++ tailWord_60079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60079).length < 2 ^ (prefixWord ++ tailWord_60079).sum := by decide
  have hdescent : baseEnd_60079 < baseStart_60079 := by decide
  rcases family_descends (prefixWord ++ tailWord_60079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60083 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 1, 3]
def baseStart_60083 : Nat := 118140960795 + 60083 * 2 ^ 59
def prefixEnd_60083 : Nat := 4983230072969 + 3 ^ 40 * 60083 * 2
def baseEnd_60083 : Nat := 20567638776129105790793

theorem tailTrace_60083 : CollatzResearch.WordTrace tailWord_60083 prefixEnd_60083 20567638776129105790793 := by
  unfold tailWord_60083
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191407041337027204560903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460938027558018136373935 2191407041337027204560903)
  ·
    refine ⟨3287110562005540806841355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191407041337027204560903 3287110562005540806841355)
    ·
      refine ⟨4930665843008311210262033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287110562005540806841355 4930665843008311210262033)
      ·
        refine ⟨3697999382256233407696525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930665843008311210262033 3697999382256233407696525)
        ·
          refine ⟨1386749768346087527886197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697999382256233407696525 1386749768346087527886197)
          ·
            refine ⟨130007790782445705739331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1386749768346087527886197 130007790782445705739331)
            ·
              refine ⟨195011686173668558608997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130007790782445705739331 195011686173668558608997)
              ·
                refine ⟨36564691157562854739187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195011686173668558608997 36564691157562854739187)
                ·
                  refine ⟨54847036736344282108781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36564691157562854739187 54847036736344282108781)
                  ·
                    refine ⟨20567638776129105790793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54847036736344282108781 20567638776129105790793)
                    ·
                      rfl

theorem cell22_60083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 3].length) (baseStart_60083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60083 prefixEnd_60083 := by exact prefixLift 60083
  have htrace : WordTrace (prefixWord ++ tailWord_60083) baseStart_60083 baseEnd_60083 := by
    simpa [prefixWord, tailWord_60083, baseEnd_60083] using wordTrace_append hprefix tailTrace_60083
  have hstable : (prefixWord ++ tailWord_60083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60083).length < 2 ^ (prefixWord ++ tailWord_60083).sum := by decide
  have hdescent : baseEnd_60083 < baseStart_60083 := by decide
  rcases family_descends (prefixWord ++ tailWord_60083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60117 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_60117 : Nat := 118140960795 + 60117 * 2 ^ 59
def prefixEnd_60117 : Nat := 4983230072969 + 3 ^ 40 * 60117 * 2
def baseEnd_60117 : Nat := 20579277670964350440689

theorem tailTrace_60117 : CollatzResearch.WordTrace tailWord_60117 prefixEnd_60117 20579277670964350440689 := by
  unfold tailWord_60117
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192647123213851011298605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1461764748809234007532403 2192647123213851011298605)
  ·
    refine ⟨822242671205194129236977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2192647123213851011298605 822242671205194129236977)
    ·
      refine ⟨616682003403895596927733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822242671205194129236977 616682003403895596927733)
      ·
        refine ⟨57813937819115212211975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 616682003403895596927733 57813937819115212211975)
        ·
          refine ⟨86720906728672818317963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57813937819115212211975 86720906728672818317963)
          ·
            refine ⟨130081360093009227476945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86720906728672818317963 130081360093009227476945)
            ·
              refine ⟨97561020069756920607709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130081360093009227476945 97561020069756920607709)
              ·
                refine ⟨36585382526158845227891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97561020069756920607709 36585382526158845227891)
                ·
                  refine ⟨54878073789238267841837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36585382526158845227891 54878073789238267841837)
                  ·
                    refine ⟨20579277670964350440689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54878073789238267841837 20579277670964350440689)
                    ·
                      rfl

theorem cell22_60117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_60117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60117 prefixEnd_60117 := by exact prefixLift 60117
  have htrace : WordTrace (prefixWord ++ tailWord_60117) baseStart_60117 baseEnd_60117 := by
    simpa [prefixWord, tailWord_60117, baseEnd_60117] using wordTrace_append hprefix tailTrace_60117
  have hstable : (prefixWord ++ tailWord_60117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60117).length < 2 ^ (prefixWord ++ tailWord_60117).sum := by decide
  have hdescent : baseEnd_60117 < baseStart_60117 := by decide
  rcases family_descends (prefixWord ++ tailWord_60117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60141 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 6]
def baseStart_60141 : Nat := 118140960795 + 60141 * 2 ^ 59
def prefixEnd_60141 : Nat := 4983230072969 + 3 ^ 40 * 60141 * 2
def baseEnd_60141 : Nat := 6862497787145429280205

theorem tailTrace_60141 : CollatzResearch.WordTrace tailWord_60141 prefixEnd_60141 6862497787145429280205 := by
  unfold tailWord_60141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193522475126903110172277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1462348316751268740114851 2193522475126903110172277)
  ·
    refine ⟨205642732043147166578651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2193522475126903110172277 205642732043147166578651)
    ·
      refine ⟨308464098064720749867977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205642732043147166578651 308464098064720749867977)
      ·
        refine ⟨231348073548540562400983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308464098064720749867977 231348073548540562400983)
        ·
          refine ⟨347022110322810843601475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231348073548540562400983 347022110322810843601475)
          ·
            refine ⟨520533165484216265402213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347022110322810843601475 520533165484216265402213)
            ·
              refine ⟨97599968528290549762915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520533165484216265402213 97599968528290549762915)
              ·
                refine ⟨146399952792435824644373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97599968528290549762915 146399952792435824644373)
                ·
                  refine ⟨6862497787145429280205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146399952792435824644373 6862497787145429280205)
                  ·
                    rfl

theorem cell22_60141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_60141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60141 prefixEnd_60141 := by exact prefixLift 60141
  have htrace : WordTrace (prefixWord ++ tailWord_60141) baseStart_60141 baseEnd_60141 := by
    simpa [prefixWord, tailWord_60141, baseEnd_60141] using wordTrace_append hprefix tailTrace_60141
  have hstable : (prefixWord ++ tailWord_60141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60141).length < 2 ^ (prefixWord ++ tailWord_60141).sum := by decide
  have hdescent : baseEnd_60141 < baseStart_60141 := by decide
  rcases family_descends (prefixWord ++ tailWord_60141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60154 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_60154 : Nat := 118140960795 + 60154 * 2 ^ 59
def prefixEnd_60154 : Nat := 4983230072969 + 3 ^ 40 * 60154 * 2
def baseEnd_60154 : Nat := 20591943527108587265575

theorem tailTrace_60154 : CollatzResearch.WordTrace tailWord_60154 prefixEnd_60154 20591943527108587265575 := by
  unfold tailWord_60154
  simp only [CollatzResearch.WordTrace]
  refine ⟨548499156019951582598879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1462664416053204220263677 548499156019951582598879)
  ·
    refine ⟨822748734029927373898319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548499156019951582598879 822748734029927373898319)
    ·
      refine ⟨1234123101044891060847479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822748734029927373898319 1234123101044891060847479)
      ·
        refine ⟨1851184651567336591271219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234123101044891060847479 1851184651567336591271219)
        ·
          refine ⟨2776776977351004886906829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851184651567336591271219 2776776977351004886906829)
          ·
            refine ⟨1041291366506626832590061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2776776977351004886906829 1041291366506626832590061)
            ·
              refine ⟨390484262439985062221273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041291366506626832590061 390484262439985062221273)
              ·
                refine ⟨292863196829988796665955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390484262439985062221273 292863196829988796665955)
                ·
                  refine ⟨439294795244983194998933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292863196829988796665955 439294795244983194998933)
                  ·
                    refine ⟨20591943527108587265575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 439294795244983194998933 20591943527108587265575)
                    ·
                      rfl

theorem cell22_60154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_60154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60154 prefixEnd_60154 := by exact prefixLift 60154
  have htrace : WordTrace (prefixWord ++ tailWord_60154) baseStart_60154 baseEnd_60154 := by
    simpa [prefixWord, tailWord_60154, baseEnd_60154] using wordTrace_append hprefix tailTrace_60154
  have hstable : (prefixWord ++ tailWord_60154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60154).length < 2 ^ (prefixWord ++ tailWord_60154).sum := by decide
  have hdescent : baseEnd_60154 < baseStart_60154 := by decide
  rcases family_descends (prefixWord ++ tailWord_60154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60156 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_60156 : Nat := 118140960795 + 60156 * 2 ^ 59
def prefixEnd_60156 : Nat := 4983230072969 + 3 ^ 40 * 60156 * 2
def baseEnd_60156 : Nat := 20592628167981248715569

theorem tailTrace_60156 : CollatzResearch.WordTrace tailWord_60156 prefixEnd_60156 20592628167981248715569 := by
  unfold tailWord_60156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097034785036280335984161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1462713046715040447978881 1097034785036280335984161)
  ·
    refine ⟨822776088777210251988121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1097034785036280335984161 822776088777210251988121)
    ·
      refine ⟨617082066582907688991091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822776088777210251988121 617082066582907688991091)
      ·
        refine ⟨925623099874361533486637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617082066582907688991091 925623099874361533486637)
        ·
          refine ⟨347108662452885575057489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925623099874361533486637 347108662452885575057489)
          ·
            refine ⟨260331496839664181293117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347108662452885575057489 260331496839664181293117)
            ·
              refine ⟨97624311314874067984919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260331496839664181293117 97624311314874067984919)
              ·
                refine ⟨146436466972311101977379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97624311314874067984919 146436466972311101977379)
                ·
                  refine ⟨219654700458466652966069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146436466972311101977379 219654700458466652966069)
                  ·
                    refine ⟨20592628167981248715569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 219654700458466652966069 20592628167981248715569)
                    ·
                      rfl

theorem cell22_60156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_60156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60156 prefixEnd_60156 := by exact prefixLift 60156
  have htrace : WordTrace (prefixWord ++ tailWord_60156) baseStart_60156 baseEnd_60156 := by
    simpa [prefixWord, tailWord_60156, baseEnd_60156] using wordTrace_append hprefix tailTrace_60156
  have hstable : (prefixWord ++ tailWord_60156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60156).length < 2 ^ (prefixWord ++ tailWord_60156).sum := by decide
  have hdescent : baseEnd_60156 < baseStart_60156 := by decide
  rcases family_descends (prefixWord ++ tailWord_60156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60229 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_60229 : Nat := 118140960795 + 60229 * 2 ^ 59
def prefixEnd_60229 : Nat := 4983230072969 + 3 ^ 40 * 60229 * 2
def baseEnd_60229 : Nat := 20617617559833391640345

theorem tailTrace_60229 : CollatzResearch.WordTrace tailWord_60229 prefixEnd_60229 20617617559833391640345 := by
  unfold tailWord_60229
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196732098808094139375741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1464488065872062759583827 2196732098808094139375741)
  ·
    refine ⟨823774537053035302265903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2196732098808094139375741 823774537053035302265903)
    ·
      refine ⟨1235661805579552953398855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823774537053035302265903 1235661805579552953398855)
      ·
        refine ⟨1853492708369329430098283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235661805579552953398855 1853492708369329430098283)
        ·
          refine ⟨2780239062553994145147425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853492708369329430098283 2780239062553994145147425)
          ·
            refine ⟨2085179296915495608860569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2780239062553994145147425 2085179296915495608860569)
            ·
              refine ⟨1563884472686621706645427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085179296915495608860569 1563884472686621706645427)
              ·
                refine ⟨2345826709029932559968141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1563884472686621706645427 2345826709029932559968141)
                ·
                  refine ⟨879685015886224709988053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2345826709029932559968141 879685015886224709988053)
                  ·
                    refine ⟨20617617559833391640345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 879685015886224709988053 20617617559833391640345)
                    ·
                      rfl

theorem cell22_60229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_60229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60229 prefixEnd_60229 := by exact prefixLift 60229
  have htrace : WordTrace (prefixWord ++ tailWord_60229) baseStart_60229 baseEnd_60229 := by
    simpa [prefixWord, tailWord_60229, baseEnd_60229] using wordTrace_append hprefix tailTrace_60229
  have hstable : (prefixWord ++ tailWord_60229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60229).length < 2 ^ (prefixWord ++ tailWord_60229).sum := by decide
  have hdescent : baseEnd_60229 < baseStart_60229 := by decide
  rcases family_descends (prefixWord ++ tailWord_60229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60252 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_60252 : Nat := 118140960795 + 60252 * 2 ^ 59
def prefixEnd_60252 : Nat := 4983230072969 + 3 ^ 40 * 60252 * 2
def baseEnd_60252 : Nat := 20625490929868998315275

theorem tailTrace_60252 : CollatzResearch.WordTrace tailWord_60252 prefixEnd_60252 20625490929868998315275 := by
  unfold tailWord_60252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098785488862384533731505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1465047318483179378308673 1098785488862384533731505)
  ·
    refine ⟨824089116646788400298629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1098785488862384533731505 824089116646788400298629)
    ·
      refine ⟨154516709371272825055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 824089116646788400298629 154516709371272825055993)
      ·
        refine ⟨115887532028454618791995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154516709371272825055993 115887532028454618791995)
        ·
          refine ⟨173831298042681928187993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115887532028454618791995 173831298042681928187993)
          ·
            refine ⟨130373473532011446140995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173831298042681928187993 130373473532011446140995)
            ·
              refine ⟨195560210298017169211493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130373473532011446140995 195560210298017169211493)
              ·
                refine ⟨36667539430878219227155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195560210298017169211493 36667539430878219227155)
                ·
                  refine ⟨55001309146317328840733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36667539430878219227155 55001309146317328840733)
                  ·
                    refine ⟨20625490929868998315275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55001309146317328840733 20625490929868998315275)
                    ·
                      rfl

theorem cell22_60252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_60252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60252 prefixEnd_60252 := by exact prefixLift 60252
  have htrace : WordTrace (prefixWord ++ tailWord_60252) baseStart_60252 baseEnd_60252 := by
    simpa [prefixWord, tailWord_60252, baseEnd_60252] using wordTrace_append hprefix tailTrace_60252
  have hstable : (prefixWord ++ tailWord_60252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60252).length < 2 ^ (prefixWord ++ tailWord_60252).sum := by decide
  have hdescent : baseEnd_60252 < baseStart_60252 := by decide
  rcases family_descends (prefixWord ++ tailWord_60252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60261 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_60261 : Nat := 118140960795 + 60261 * 2 ^ 59
def prefixEnd_60261 : Nat := 4983230072969 + 3 ^ 40 * 60261 * 2
def baseEnd_60261 : Nat := 20628571813795974840247

theorem tailTrace_60261 : CollatzResearch.WordTrace tailWord_60261 prefixEnd_60261 20628571813795974840247 := by
  unfold tailWord_60261
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197899234692163604540637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465266156461442403027091 2197899234692163604540637)
  ·
    refine ⟨824212213009561351702739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2197899234692163604540637 824212213009561351702739)
    ·
      refine ⟨1236318319514342027554109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824212213009561351702739 1236318319514342027554109)
      ·
        refine ⟨463619369817878260332791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1236318319514342027554109 463619369817878260332791)
        ·
          refine ⟨695429054726817390499187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463619369817878260332791 695429054726817390499187)
          ·
            refine ⟨1043143582090226085748781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695429054726817390499187 1043143582090226085748781)
            ·
              refine ⟨391178843283834782155793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1043143582090226085748781 391178843283834782155793)
              ·
                refine ⟨293384132462876086616845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391178843283834782155793 293384132462876086616845)
                ·
                  refine ⟨110019049673578532481317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293384132462876086616845 110019049673578532481317)
                  ·
                    refine ⟨20628571813795974840247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110019049673578532481317 20628571813795974840247)
                    ·
                      rfl

theorem cell22_60261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_60261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60261 prefixEnd_60261 := by exact prefixLift 60261
  have htrace : WordTrace (prefixWord ++ tailWord_60261) baseStart_60261 baseEnd_60261 := by
    simpa [prefixWord, tailWord_60261, baseEnd_60261] using wordTrace_append hprefix tailTrace_60261
  have hstable : (prefixWord ++ tailWord_60261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60261).length < 2 ^ (prefixWord ++ tailWord_60261).sum := by decide
  have hdescent : baseEnd_60261 < baseStart_60261 := by decide
  rcases family_descends (prefixWord ++ tailWord_60261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60291 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_60291 : Nat := 118140960795 + 60291 * 2 ^ 59
def prefixEnd_60291 : Nat := 4983230072969 + 3 ^ 40 * 60291 * 2
def baseEnd_60291 : Nat := 20638841426885896590155

theorem tailTrace_60291 : CollatzResearch.WordTrace tailWord_60291 prefixEnd_60291 20638841426885896590155 := by
  unfold tailWord_60291
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198993424583478728132727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465995616388985818755151 2198993424583478728132727)
  ·
    refine ⟨3298490136875218092199091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198993424583478728132727 3298490136875218092199091)
    ·
      refine ⟨4947735205312827138298637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298490136875218092199091 4947735205312827138298637)
      ·
        refine ⟨1855400701992310176861989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4947735205312827138298637 1855400701992310176861989)
        ·
          refine ⟨347887631623558158161623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1855400701992310176861989 347887631623558158161623)
          ·
            refine ⟨521831447435337237242435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347887631623558158161623 521831447435337237242435)
            ·
              refine ⟨782747171153005855863653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521831447435337237242435 782747171153005855863653)
              ·
                refine ⟨146765094591188597974435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782747171153005855863653 146765094591188597974435)
                ·
                  refine ⟨220147641886782896961653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146765094591188597974435 220147641886782896961653)
                  ·
                    refine ⟨20638841426885896590155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220147641886782896961653 20638841426885896590155)
                    ·
                      rfl

theorem cell22_60291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_60291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60291 prefixEnd_60291 := by exact prefixLift 60291
  have htrace : WordTrace (prefixWord ++ tailWord_60291) baseStart_60291 baseEnd_60291 := by
    simpa [prefixWord, tailWord_60291, baseEnd_60291] using wordTrace_append hprefix tailTrace_60291
  have hstable : (prefixWord ++ tailWord_60291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60291).length < 2 ^ (prefixWord ++ tailWord_60291).sum := by decide
  have hdescent : baseEnd_60291 < baseStart_60291 := by decide
  rcases family_descends (prefixWord ++ tailWord_60291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60293 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 4]
def baseStart_60293 : Nat := 118140960795 + 60293 * 2 ^ 59
def prefixEnd_60293 : Nat := 4983230072969 + 3 ^ 40 * 60293 * 2
def baseEnd_60293 : Nat := 6879842022586186013383

theorem tailTrace_60293 : CollatzResearch.WordTrace tailWord_60293 prefixEnd_60293 6879842022586186013383 := by
  unfold tailWord_60293
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199066370576233069705533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1466044247050822046470355 2199066370576233069705533)
  ·
    refine ⟨824649888966087401139575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2199066370576233069705533 824649888966087401139575)
    ·
      refine ⟨1236974833449131101709363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824649888966087401139575 1236974833449131101709363)
      ·
        refine ⟨1855462250173696652564045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236974833449131101709363 1855462250173696652564045)
        ·
          refine ⟨695798343815136244711517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1855462250173696652564045 695798343815136244711517)
          ·
            refine ⟨260924378930676091766819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695798343815136244711517 260924378930676091766819)
            ·
              refine ⟨391386568396014137650229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260924378930676091766819 391386568396014137650229)
              ·
                refine ⟨36692490787126325404709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391386568396014137650229 36692490787126325404709)
                ·
                  refine ⟨6879842022586186013383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36692490787126325404709 6879842022586186013383)
                  ·
                    rfl

theorem cell22_60293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_60293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60293 prefixEnd_60293 := by exact prefixLift 60293
  have htrace : WordTrace (prefixWord ++ tailWord_60293) baseStart_60293 baseEnd_60293 := by
    simpa [prefixWord, tailWord_60293, baseEnd_60293] using wordTrace_append hprefix tailTrace_60293
  have hstable : (prefixWord ++ tailWord_60293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60293).length < 2 ^ (prefixWord ++ tailWord_60293).sum := by decide
  have hdescent : baseEnd_60293 < baseStart_60293 := by decide
  rcases family_descends (prefixWord ++ tailWord_60293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60295 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 1, 4]
def baseStart_60295 : Nat := 118140960795 + 60295 * 2 ^ 59
def prefixEnd_60295 : Nat := 4983230072969 + 3 ^ 40 * 60295 * 2
def baseEnd_60295 : Nat := 20640210708631219490143

theorem tailTrace_60295 : CollatzResearch.WordTrace tailWord_60295 prefixEnd_60295 20640210708631219490143 := by
  unfold tailWord_60295
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199139316568987411278339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1466092877712658274185559 2199139316568987411278339)
  ·
    refine ⟨3298708974853481116917509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199139316568987411278339 3298708974853481116917509)
    ·
      refine ⟨618507932785027709422033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3298708974853481116917509 618507932785027709422033)
      ·
        refine ⟨463880949588770782066525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618507932785027709422033 463880949588770782066525)
        ·
          refine ⟨173955356095789043274947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463880949588770782066525 173955356095789043274947)
          ·
            refine ⟨260933034143683564912421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173955356095789043274947 260933034143683564912421)
            ·
              refine ⟨48924943901940668421079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260933034143683564912421 48924943901940668421079)
              ·
                refine ⟨73387415852911002631619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48924943901940668421079 73387415852911002631619)
                ·
                  refine ⟨110081123779366503947429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73387415852911002631619 110081123779366503947429)
                  ·
                    refine ⟨20640210708631219490143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110081123779366503947429 20640210708631219490143)
                    ·
                      rfl

theorem cell22_60295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_60295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60295 prefixEnd_60295 := by exact prefixLift 60295
  have htrace : WordTrace (prefixWord ++ tailWord_60295) baseStart_60295 baseEnd_60295 := by
    simpa [prefixWord, tailWord_60295, baseEnd_60295] using wordTrace_append hprefix tailTrace_60295
  have hstable : (prefixWord ++ tailWord_60295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60295).length < 2 ^ (prefixWord ++ tailWord_60295).sum := by decide
  have hdescent : baseEnd_60295 < baseStart_60295 := by decide
  rcases family_descends (prefixWord ++ tailWord_60295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60340 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_60340 : Nat := 118140960795 + 60340 * 2 ^ 59
def prefixEnd_60340 : Nat := 4983230072969 + 3 ^ 40 * 60340 * 2
def baseEnd_60340 : Nat := 20655615128266102115005

theorem tailTrace_60340 : CollatzResearch.WordTrace tailWord_60340 prefixEnd_60340 20655615128266102115005 := by
  unfold tailWord_60340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100390300702980048333237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1467187067603973397777649 1100390300702980048333237)
  ·
    refine ⟨103161590690904379531241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1100390300702980048333237 103161590690904379531241)
    ·
      refine ⟨77371193018178284648431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103161590690904379531241 77371193018178284648431)
      ·
        refine ⟨116056789527267426972647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77371193018178284648431 116056789527267426972647)
        ·
          refine ⟨174085184290901140458971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116056789527267426972647 174085184290901140458971)
          ·
            refine ⟨261127776436351710688457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174085184290901140458971 261127776436351710688457)
            ·
              refine ⟨195845832327263783016343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261127776436351710688457 195845832327263783016343)
              ·
                refine ⟨293768748490895674524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195845832327263783016343 293768748490895674524515)
                ·
                  refine ⟨440653122736343511786773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293768748490895674524515 440653122736343511786773)
                  ·
                    refine ⟨20655615128266102115005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 440653122736343511786773 20655615128266102115005)
                    ·
                      rfl

theorem cell22_60340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_60340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60340 prefixEnd_60340 := by exact prefixLift 60340
  have htrace : WordTrace (prefixWord ++ tailWord_60340) baseStart_60340 baseEnd_60340 := by
    simpa [prefixWord, tailWord_60340, baseEnd_60340] using wordTrace_append hprefix tailTrace_60340
  have hstable : (prefixWord ++ tailWord_60340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60340).length < 2 ^ (prefixWord ++ tailWord_60340).sum := by decide
  have hdescent : baseEnd_60340 < baseStart_60340 := by decide
  rcases family_descends (prefixWord ++ tailWord_60340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60445 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 6]
def baseStart_60445 : Nat := 118140960795 + 60445 * 2 ^ 59
def prefixEnd_60445 : Nat := 4983230072969 + 3 ^ 40 * 60445 * 2
def baseEnd_60445 : Nat := 6897186258026942746561

theorem tailTrace_60445 : CollatzResearch.WordTrace tailWord_60445 prefixEnd_60445 6897186258026942746561 := by
  unfold tailWord_60445
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204610266025563029238789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469740177350375352825859 2204610266025563029238789)
  ·
    refine ⟨413364424879793067982273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2204610266025563029238789 413364424879793067982273)
    ·
      refine ⟨310023318659844800986705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413364424879793067982273 310023318659844800986705)
      ·
        refine ⟨232517488994883600740029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310023318659844800986705 232517488994883600740029)
        ·
          refine ⟨87194058373081350277511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232517488994883600740029 87194058373081350277511)
          ·
            refine ⟨130791087559622025416267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87194058373081350277511 130791087559622025416267)
            ·
              refine ⟨196186631339433038124401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130791087559622025416267 196186631339433038124401)
              ·
                refine ⟨147139973504574778593301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196186631339433038124401 147139973504574778593301)
                ·
                  refine ⟨6897186258026942746561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147139973504574778593301 6897186258026942746561)
                  ·
                    rfl

theorem cell22_60445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_60445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60445 prefixEnd_60445 := by exact prefixLift 60445
  have htrace : WordTrace (prefixWord ++ tailWord_60445) baseStart_60445 baseEnd_60445 := by
    simpa [prefixWord, tailWord_60445, baseEnd_60445] using wordTrace_append hprefix tailTrace_60445
  have hstable : (prefixWord ++ tailWord_60445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60445).length < 2 ^ (prefixWord ++ tailWord_60445).sum := by decide
  have hdescent : baseEnd_60445 < baseStart_60445 := by decide
  rcases family_descends (prefixWord ++ tailWord_60445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60462 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_60462 : Nat := 118140960795 + 60462 * 2 ^ 59
def prefixEnd_60462 : Nat := 4983230072969 + 3 ^ 40 * 60462 * 2
def baseEnd_60462 : Nat := 6899126073832816854877

theorem tailTrace_60462 : CollatzResearch.WordTrace tailWord_60462 prefixEnd_60462 6899126073832816854877 := by
  unfold tailWord_60462
  simp only [CollatzResearch.WordTrace]
  refine ⟨275653788370496866575955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1470153537975983288405093 275653788370496866575955)
  ·
    refine ⟨413480682555745299863933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275653788370496866575955 413480682555745299863933)
    ·
      refine ⟨155055255958404487448975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413480682555745299863933 155055255958404487448975)
      ·
        refine ⟨232582883937606731173463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155055255958404487448975 232582883937606731173463)
        ·
          refine ⟨348874325906410096760195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232582883937606731173463 348874325906410096760195)
          ·
            refine ⟨523311488859615145140293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348874325906410096760195 523311488859615145140293)
            ·
              refine ⟨98120904161177839713805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523311488859615145140293 98120904161177839713805)
              ·
                refine ⟨36795339060441689892677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98120904161177839713805 36795339060441689892677)
                ·
                  refine ⟨6899126073832816854877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36795339060441689892677 6899126073832816854877)
                  ·
                    rfl

theorem cell22_60462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_60462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60462 prefixEnd_60462 := by exact prefixLift 60462
  have htrace : WordTrace (prefixWord ++ tailWord_60462) baseStart_60462 baseEnd_60462 := by
    simpa [prefixWord, tailWord_60462, baseEnd_60462] using wordTrace_append hprefix tailTrace_60462
  have hstable : (prefixWord ++ tailWord_60462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60462).length < 2 ^ (prefixWord ++ tailWord_60462).sum := by decide
  have hdescent : baseEnd_60462 < baseStart_60462 := by decide
  rcases family_descends (prefixWord ++ tailWord_60462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60473 : List Nat := [1, 2, 1, 5, 2, 2, 9]
def baseStart_60473 : Nat := 118140960795 + 60473 * 2 ^ 59
def prefixEnd_60473 : Nat := 4983230072969 + 3 ^ 40 * 60473 * 2
def baseEnd_60473 : Nat := 766709027640669945911

theorem tailTrace_60473 : CollatzResearch.WordTrace tailWord_60473 prefixEnd_60473 766709027640669945911 := by
  unfold tailWord_60473
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205631509924123811258073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1470421006616082540838715 2205631509924123811258073)
  ·
    refine ⟨1654223632443092858443555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2205631509924123811258073 1654223632443092858443555)
    ·
      refine ⟨2481335448664639287665333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654223632443092858443555 2481335448664639287665333)
      ·
        refine ⟨232625198312309933218625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2481335448664639287665333 232625198312309933218625)
        ·
          refine ⟨174468898734232449913969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232625198312309933218625 174468898734232449913969)
          ·
            refine ⟨130851674050674337435477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174468898734232449913969 130851674050674337435477)
            ·
              refine ⟨766709027640669945911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 130851674050674337435477 766709027640669945911)
              ·
                rfl

theorem cell22_60473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 9].length) (baseStart_60473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60473 prefixEnd_60473 := by exact prefixLift 60473
  have htrace : WordTrace (prefixWord ++ tailWord_60473) baseStart_60473 baseEnd_60473 := by
    simpa [prefixWord, tailWord_60473, baseEnd_60473] using wordTrace_append hprefix tailTrace_60473
  have hstable : (prefixWord ++ tailWord_60473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60473).length < 2 ^ (prefixWord ++ tailWord_60473).sum := by decide
  have hdescent : baseEnd_60473 < baseStart_60473 := by decide
  rcases family_descends (prefixWord ++ tailWord_60473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60477 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_60477 : Nat := 118140960795 + 60477 * 2 ^ 59
def prefixEnd_60477 : Nat := 4983230072969 + 3 ^ 40 * 60477 * 2
def baseEnd_60477 : Nat := 20702513028043411439585

theorem tailTrace_60477 : CollatzResearch.WordTrace tailWord_60477 prefixEnd_60477 20702513028043411439585 := by
  unfold tailWord_60477
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205777401909632494403685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1470518267939754996269123 2205777401909632494403685)
  ·
    refine ⟨413583262858056092700691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2205777401909632494403685 413583262858056092700691)
    ·
      refine ⟨620374894287084139051037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413583262858056092700691 620374894287084139051037)
      ·
        refine ⟨232640585357656552144139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620374894287084139051037 232640585357656552144139)
        ·
          refine ⟨348960878036484828216209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232640585357656552144139 348960878036484828216209)
          ·
            refine ⟨261720658527363621162157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348960878036484828216209 261720658527363621162157)
            ·
              refine ⟨98145246947761357935809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261720658527363621162157 98145246947761357935809)
              ·
                refine ⟨73608935210821018451857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98145246947761357935809 73608935210821018451857)
                ·
                  refine ⟨55206701408115763838893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73608935210821018451857 55206701408115763838893)
                  ·
                    refine ⟨20702513028043411439585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55206701408115763838893 20702513028043411439585)
                    ·
                      rfl

theorem cell22_60477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_60477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60477 prefixEnd_60477 := by exact prefixLift 60477
  have htrace : WordTrace (prefixWord ++ tailWord_60477) baseStart_60477 baseEnd_60477 := by
    simpa [prefixWord, tailWord_60477, baseEnd_60477] using wordTrace_append hprefix tailTrace_60477
  have hstable : (prefixWord ++ tailWord_60477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60477).length < 2 ^ (prefixWord ++ tailWord_60477).sum := by decide
  have hdescent : baseEnd_60477 < baseStart_60477 := by decide
  rcases family_descends (prefixWord ++ tailWord_60477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60552 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_60552 : Nat := 118140960795 + 60552 * 2 ^ 59
def prefixEnd_60552 : Nat := 4983230072969 + 3 ^ 40 * 60552 * 2
def baseEnd_60552 : Nat := 6909395686922738604785

theorem tailTrace_60552 : CollatzResearch.WordTrace tailWord_60552 prefixEnd_60552 6909395686922738604785 := by
  unfold tailWord_60552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104256438318960151691955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1472341917758613535589273 1104256438318960151691955)
  ·
    refine ⟨1656384657478440227537933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104256438318960151691955 1656384657478440227537933)
    ·
      refine ⟨621144246554415085326725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1656384657478440227537933 621144246554415085326725)
      ·
        refine ⟨116464546228952828498761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 621144246554415085326725 116464546228952828498761)
        ·
          refine ⟨87348409671714621374071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116464546228952828498761 87348409671714621374071)
          ·
            refine ⟨131022614507571932061107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87348409671714621374071 131022614507571932061107)
            ·
              refine ⟨196533921761357898091661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131022614507571932061107 196533921761357898091661)
              ·
                refine ⟨73700220660509211784373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196533921761357898091661 73700220660509211784373)
                ·
                  refine ⟨6909395686922738604785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73700220660509211784373 6909395686922738604785)
                  ·
                    rfl

theorem cell22_60552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_60552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60552 prefixEnd_60552 := by exact prefixLift 60552
  have htrace : WordTrace (prefixWord ++ tailWord_60552) baseStart_60552 baseEnd_60552 := by
    simpa [prefixWord, tailWord_60552, baseEnd_60552] using wordTrace_append hprefix tailTrace_60552
  have hstable : (prefixWord ++ tailWord_60552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60552).length < 2 ^ (prefixWord ++ tailWord_60552).sum := by decide
  have hdescent : baseEnd_60552 < baseStart_60552 := by decide
  rcases family_descends (prefixWord ++ tailWord_60552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60563 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 6]
def baseStart_60563 : Nat := 118140960795 + 60563 * 2 ^ 59
def prefixEnd_60563 : Nat := 4983230072969 + 3 ^ 40 * 60563 * 2
def baseEnd_60563 : Nat := 6910650861855951263107

theorem tailTrace_60563 : CollatzResearch.WordTrace tailWord_60563 prefixEnd_60563 6910650861855951263107 := by
  unfold tailWord_60563
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208914079598069182034343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1472609386398712788022895 2208914079598069182034343)
  ·
    refine ⟨3313371119397103773051515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208914079598069182034343 3313371119397103773051515)
    ·
      refine ⟨4970056679095655659577273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313371119397103773051515 4970056679095655659577273)
      ·
        refine ⟨3727542509321741744682955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4970056679095655659577273 3727542509321741744682955)
        ·
          refine ⟨5591313763982612617024433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727542509321741744682955 5591313763982612617024433)
          ·
            refine ⟨4193485322986959462768325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591313763982612617024433 4193485322986959462768325)
            ·
              refine ⟨786278498060054899269061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4193485322986959462768325 786278498060054899269061)
              ·
                refine ⟨147427218386260293612949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786278498060054899269061 147427218386260293612949)
                ·
                  refine ⟨6910650861855951263107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147427218386260293612949 6910650861855951263107)
                  ·
                    rfl

theorem cell22_60563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_60563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60563 prefixEnd_60563 := by exact prefixLift 60563
  have htrace : WordTrace (prefixWord ++ tailWord_60563) baseStart_60563 baseEnd_60563 := by
    simpa [prefixWord, tailWord_60563, baseEnd_60563] using wordTrace_append hprefix tailTrace_60563
  have hstable : (prefixWord ++ tailWord_60563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60563).length < 2 ^ (prefixWord ++ tailWord_60563).sum := by decide
  have hdescent : baseEnd_60563 < baseStart_60563 := by decide
  rcases family_descends (prefixWord ++ tailWord_60563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60565 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_60565 : Nat := 118140960795 + 60565 * 2 ^ 59
def prefixEnd_60565 : Nat := 4983230072969 + 3 ^ 40 * 60565 * 2
def baseEnd_60565 : Nat := 20732637226440515239315

theorem tailTrace_60565 : CollatzResearch.WordTrace tailWord_60565 prefixEnd_60565 20732637226440515239315 := by
  unfold tailWord_60565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208987025590823523607149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1472658017060549015738099 2208987025590823523607149)
  ·
    refine ⟨828370134596558821352681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2208987025590823523607149 828370134596558821352681)
    ·
      refine ⟨621277600947419116014511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828370134596558821352681 621277600947419116014511)
      ·
        refine ⟨931916401421128674021767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621277600947419116014511 931916401421128674021767)
        ·
          refine ⟨1397874602131693011032651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931916401421128674021767 1397874602131693011032651)
          ·
            refine ⟨2096811903197539516548977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397874602131693011032651 2096811903197539516548977)
            ·
              refine ⟨1572608927398154637411733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096811903197539516548977 1572608927398154637411733)
              ·
                refine ⟨73716043471788498628675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1572608927398154637411733 73716043471788498628675)
                ·
                  refine ⟨110574065207682747943013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73716043471788498628675 110574065207682747943013)
                  ·
                    refine ⟨20732637226440515239315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110574065207682747943013 20732637226440515239315)
                    ·
                      rfl

theorem cell22_60565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_60565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60565 prefixEnd_60565 := by exact prefixLift 60565
  have htrace : WordTrace (prefixWord ++ tailWord_60565) baseStart_60565 baseEnd_60565 := by
    simpa [prefixWord, tailWord_60565, baseEnd_60565] using wordTrace_append hprefix tailTrace_60565
  have hstable : (prefixWord ++ tailWord_60565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60565).length < 2 ^ (prefixWord ++ tailWord_60565).sum := by decide
  have hdescent : baseEnd_60565 < baseStart_60565 := by decide
  rcases family_descends (prefixWord ++ tailWord_60565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60595 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 4, 3]
def baseStart_60595 : Nat := 118140960795 + 60595 * 2 ^ 59
def prefixEnd_60595 : Nat := 4983230072969 + 3 ^ 40 * 60595 * 2
def baseEnd_60595 : Nat := 20742906839530436989223

theorem tailTrace_60595 : CollatzResearch.WordTrace tailWord_60595 prefixEnd_60595 20742906839530436989223 := by
  unfold tailWord_60595
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210081215482138647199239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1473387476988092431466159 2210081215482138647199239)
  ·
    refine ⟨3315121823223207970798859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210081215482138647199239 3315121823223207970798859)
    ·
      refine ⟨4972682734834811956198289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315121823223207970798859 4972682734834811956198289)
      ·
        refine ⟨3729512051126108967148717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972682734834811956198289 3729512051126108967148717)
        ·
          refine ⟨1398567019172290862680769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3729512051126108967148717 1398567019172290862680769)
          ·
            refine ⟨1048925264379218147010577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398567019172290862680769 1048925264379218147010577)
            ·
              refine ⟨786693948284413610257933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048925264379218147010577 786693948284413610257933)
              ·
                refine ⟨295010230606655103846725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786693948284413610257933 295010230606655103846725)
                ·
                  refine ⟨55314418238747831971261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295010230606655103846725 55314418238747831971261)
                  ·
                    refine ⟨20742906839530436989223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55314418238747831971261 20742906839530436989223)
                    ·
                      rfl

theorem cell22_60595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].length) (baseStart_60595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60595 prefixEnd_60595 := by exact prefixLift 60595
  have htrace : WordTrace (prefixWord ++ tailWord_60595) baseStart_60595 baseEnd_60595 := by
    simpa [prefixWord, tailWord_60595, baseEnd_60595] using wordTrace_append hprefix tailTrace_60595
  have hstable : (prefixWord ++ tailWord_60595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60595).length < 2 ^ (prefixWord ++ tailWord_60595).sum := by decide
  have hdescent : baseEnd_60595 < baseStart_60595 := by decide
  rcases family_descends (prefixWord ++ tailWord_60595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60623 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_60623 : Nat := 118140960795 + 60623 * 2 ^ 59
def prefixEnd_60623 : Nat := 4983230072969 + 3 ^ 40 * 60623 * 2
def baseEnd_60623 : Nat := 20752491811747697289137

theorem tailTrace_60623 : CollatzResearch.WordTrace tailWord_60623 prefixEnd_60623 20752491811747697289137 := by
  unfold tailWord_60623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211102459380699429218523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1474068306253799619479015 2211102459380699429218523)
  ·
    refine ⟨3316653689071049143827785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211102459380699429218523 3316653689071049143827785)
    ·
      refine ⟨2487490266803286857870839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3316653689071049143827785 2487490266803286857870839)
      ·
        refine ⟨3731235400204930286806259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487490266803286857870839 3731235400204930286806259)
        ·
          refine ⟨5596853100307395430209389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731235400204930286806259 5596853100307395430209389)
          ·
            refine ⟨2098819912615273286328521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5596853100307395430209389 2098819912615273286328521)
            ·
              refine ⟨1574114934461454964746391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098819912615273286328521 1574114934461454964746391)
              ·
                refine ⟨2361172401692182447119587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574114934461454964746391 2361172401692182447119587)
                ·
                  refine ⟨3541758602538273670679381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361172401692182447119587 3541758602538273670679381)
                  ·
                    refine ⟨20752491811747697289137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3541758602538273670679381 20752491811747697289137)
                    ·
                      rfl

theorem cell22_60623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_60623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60623 prefixEnd_60623 := by exact prefixLift 60623
  have htrace : WordTrace (prefixWord ++ tailWord_60623) baseStart_60623 baseEnd_60623 := by
    simpa [prefixWord, tailWord_60623, baseEnd_60623] using wordTrace_append hprefix tailTrace_60623
  have hstable : (prefixWord ++ tailWord_60623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60623).length < 2 ^ (prefixWord ++ tailWord_60623).sum := by decide
  have hdescent : baseEnd_60623 < baseStart_60623 := by decide
  rcases family_descends (prefixWord ++ tailWord_60623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60745 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_60745 : Nat := 118140960795 + 60745 * 2 ^ 59
def prefixEnd_60745 : Nat := 4983230072969 + 3 ^ 40 * 60745 * 2
def baseEnd_60745 : Nat := 20794254904980045738763

theorem tailTrace_60745 : CollatzResearch.WordTrace tailWord_60745 prefixEnd_60745 20794254904980045738763 := by
  unfold tailWord_60745
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215552164938714265159689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1477034776625809510106459 2215552164938714265159689)
  ·
    refine ⟨1661664123704035698869767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2215552164938714265159689 1661664123704035698869767)
    ·
      refine ⟨2492496185556053548304651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661664123704035698869767 2492496185556053548304651)
      ·
        refine ⟨3738744278334080322456977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492496185556053548304651 3738744278334080322456977)
        ·
          refine ⟨2804058208750560241842733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3738744278334080322456977 2804058208750560241842733)
          ·
            refine ⟨1051521828281460090691025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2804058208750560241842733 1051521828281460090691025)
            ·
              refine ⟨788641371211095068018269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051521828281460090691025 788641371211095068018269)
              ·
                refine ⟨295740514204160650506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788641371211095068018269 295740514204160650506851)
                ·
                  refine ⟨443610771306240975760277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295740514204160650506851 443610771306240975760277)
                  ·
                    refine ⟨20794254904980045738763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 443610771306240975760277 20794254904980045738763)
                    ·
                      rfl

theorem cell22_60745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_60745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60745 prefixEnd_60745 := by exact prefixLift 60745
  have htrace : WordTrace (prefixWord ++ tailWord_60745) baseStart_60745 baseEnd_60745 := by
    simpa [prefixWord, tailWord_60745, baseEnd_60745] using wordTrace_append hprefix tailTrace_60745
  have hstable : (prefixWord ++ tailWord_60745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60745).length < 2 ^ (prefixWord ++ tailWord_60745).sum := by decide
  have hdescent : baseEnd_60745 < baseStart_60745 := by decide
  rcases family_descends (prefixWord ++ tailWord_60745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60762 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_60762 : Nat := 118140960795 + 60762 * 2 ^ 59
def prefixEnd_60762 : Nat := 4983230072969 + 3 ^ 40 * 60762 * 2
def baseEnd_60762 : Nat := 20800074352397668063711

theorem tailTrace_60762 : CollatzResearch.WordTrace tailWord_60762 prefixEnd_60762 20800074352397668063711 := by
  unfold tailWord_60762
  simp only [CollatzResearch.WordTrace]
  refine ⟨554043051469281542132135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1477448137251417445685693 554043051469281542132135)
  ·
    refine ⟨831064577203922313198203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554043051469281542132135 831064577203922313198203)
    ·
      refine ⟨1246596865805883469797305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831064577203922313198203 1246596865805883469797305)
      ·
        refine ⟨934947649354412602347979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1246596865805883469797305 934947649354412602347979)
        ·
          refine ⟨1402421474031618903521969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934947649354412602347979 1402421474031618903521969)
          ·
            refine ⟨1051816105523714177641477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402421474031618903521969 1051816105523714177641477)
            ·
              refine ⟨197215519785696408307777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1051816105523714177641477 197215519785696408307777)
              ·
                refine ⟨147911639839272306230833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197215519785696408307777 147911639839272306230833)
                ·
                  refine ⟨110933729879454229673125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147911639839272306230833 110933729879454229673125)
                  ·
                    refine ⟨20800074352397668063711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110933729879454229673125 20800074352397668063711)
                    ·
                      rfl

theorem cell22_60762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_60762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60762 prefixEnd_60762 := by exact prefixLift 60762
  have htrace : WordTrace (prefixWord ++ tailWord_60762) baseStart_60762 baseEnd_60762 := by
    simpa [prefixWord, tailWord_60762, baseEnd_60762] using wordTrace_append hprefix tailTrace_60762
  have hstable : (prefixWord ++ tailWord_60762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60762).length < 2 ^ (prefixWord ++ tailWord_60762).sum := by decide
  have hdescent : baseEnd_60762 < baseStart_60762 := by decide
  rcases family_descends (prefixWord ++ tailWord_60762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60826 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_60826 : Nat := 118140960795 + 60826 * 2 ^ 59
def prefixEnd_60826 : Nat := 4983230072969 + 3 ^ 40 * 60826 * 2
def baseEnd_60826 : Nat := 20821982860322834463515

theorem tailTrace_60826 : CollatzResearch.WordTrace tailWord_60826 prefixEnd_60826 20821982860322834463515 := by
  unfold tailWord_60826
  simp only [CollatzResearch.WordTrace]
  refine ⟨554626619411316274714583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1479004318430176732572221 554626619411316274714583)
  ·
    refine ⟨831939929116974412071875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554626619411316274714583 831939929116974412071875)
    ·
      refine ⟨1247909893675461618107813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831939929116974412071875 1247909893675461618107813)
      ·
        refine ⟨233983105064149053395215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1247909893675461618107813 233983105064149053395215)
        ·
          refine ⟨350974657596223580092823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233983105064149053395215 350974657596223580092823)
          ·
            refine ⟨526461986394335370139235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350974657596223580092823 526461986394335370139235)
            ·
              refine ⟨789692979591503055208853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526461986394335370139235 789692979591503055208853)
              ·
                refine ⟨37016858418351705712915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 789692979591503055208853 37016858418351705712915)
                ·
                  refine ⟨55525287627527558569373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37016858418351705712915 55525287627527558569373)
                  ·
                    refine ⟨20821982860322834463515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55525287627527558569373 20821982860322834463515)
                    ·
                      rfl

theorem cell22_60826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_60826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60826 prefixEnd_60826 := by exact prefixLift 60826
  have htrace : WordTrace (prefixWord ++ tailWord_60826) baseStart_60826 baseEnd_60826 := by
    simpa [prefixWord, tailWord_60826, baseEnd_60826] using wordTrace_append hprefix tailTrace_60826
  have hstable : (prefixWord ++ tailWord_60826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60826).length < 2 ^ (prefixWord ++ tailWord_60826).sum := by decide
  have hdescent : baseEnd_60826 < baseStart_60826 := by decide
  rcases family_descends (prefixWord ++ tailWord_60826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60860 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_60860 : Nat := 118140960795 + 60860 * 2 ^ 59
def prefixEnd_60860 : Nat := 4983230072969 + 3 ^ 40 * 60860 * 2
def baseEnd_60860 : Nat := 20833621755158079113411

theorem tailTrace_60860 : CollatzResearch.WordTrace tailWord_60860 prefixEnd_60860 20833621755158079113411 := by
  unfold tailWord_60860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109873279761044452798017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1479831039681392603730689 1109873279761044452798017)
  ·
    refine ⟨832404959820783339598513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1109873279761044452798017 832404959820783339598513)
    ·
      refine ⟨624303719865587504698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832404959820783339598513 624303719865587504698885)
      ·
        refine ⟨117056947474797657131041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624303719865587504698885 117056947474797657131041)
        ·
          refine ⟨87792710606098242848281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117056947474797657131041 87792710606098242848281)
          ·
            refine ⟨65844532954573682136211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87792710606098242848281 65844532954573682136211)
            ·
              refine ⟨98766799431860523204317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65844532954573682136211 98766799431860523204317)
              ·
                refine ⟨37037549786947696201619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98766799431860523204317 37037549786947696201619)
                ·
                  refine ⟨55556324680421544302429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37037549786947696201619 55556324680421544302429)
                  ·
                    refine ⟨20833621755158079113411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55556324680421544302429 20833621755158079113411)
                    ·
                      rfl

theorem cell22_60860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_60860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60860 prefixEnd_60860 := by exact prefixLift 60860
  have htrace : WordTrace (prefixWord ++ tailWord_60860) baseStart_60860 baseEnd_60860 := by
    simpa [prefixWord, tailWord_60860, baseEnd_60860] using wordTrace_append hprefix tailTrace_60860
  have hstable : (prefixWord ++ tailWord_60860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60860).length < 2 ^ (prefixWord ++ tailWord_60860).sum := by decide
  have hdescent : baseEnd_60860 < baseStart_60860 := by decide
  rcases family_descends (prefixWord ++ tailWord_60860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60912 : List Nat := [2, 1, 1, 1, 3, 4, 2, 8]
def baseStart_60912 : Nat := 118140960795 + 60912 * 2 ^ 59
def prefixEnd_60912 : Nat := 4983230072969 + 3 ^ 40 * 60912 * 2
def baseEnd_60912 : Nat := 2316824713094141868139

theorem tailTrace_60912 : CollatzResearch.WordTrace tailWord_60912 prefixEnd_60912 2316824713094141868139 := by
  unfold tailWord_60912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110821577666850893244495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1481095436889134524325993 1110821577666850893244495)
  ·
    refine ⟨1666232366500276339866743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110821577666850893244495 1666232366500276339866743)
    ·
      refine ⟨2499348549750414509800115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666232366500276339866743 2499348549750414509800115)
      ·
        refine ⟨3749022824625621764700173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499348549750414509800115 3749022824625621764700173)
        ·
          refine ⟨1405883559234608161762565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3749022824625621764700173 1405883559234608161762565)
          ·
            refine ⟨263603167356489030330481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1405883559234608161762565 263603167356489030330481)
            ·
              refine ⟨197702375517366772747861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263603167356489030330481 197702375517366772747861)
              ·
                refine ⟨2316824713094141868139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 197702375517366772747861 2316824713094141868139)
                ·
                  rfl

theorem cell22_60912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_60912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60912 prefixEnd_60912 := by exact prefixLift 60912
  have htrace : WordTrace (prefixWord ++ tailWord_60912) baseStart_60912 baseEnd_60912 := by
    simpa [prefixWord, tailWord_60912, baseEnd_60912] using wordTrace_append hprefix tailTrace_60912
  have hstable : (prefixWord ++ tailWord_60912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60912).length < 2 ^ (prefixWord ++ tailWord_60912).sum := by decide
  have hdescent : baseEnd_60912 < baseStart_60912 := by decide
  rcases family_descends (prefixWord ++ tailWord_60912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60929 : List Nat := [1, 2, 4, 1, 5, 9]
def baseStart_60929 : Nat := 118140960795 + 60929 * 2 ^ 59
def prefixEnd_60929 : Nat := 4983230072969 + 3 ^ 40 * 60929 * 2
def baseEnd_60929 : Nat := 257496813151418507879

theorem tailTrace_60929 : CollatzResearch.WordTrace tailWord_60929 prefixEnd_60929 257496813151418507879 := by
  unfold tailWord_60929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222263196272113689857841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1481508797514742459905227 2222263196272113689857841)
  ·
    refine ⟨1666697397204085267393381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222263196272113689857841 1666697397204085267393381)
    ·
      refine ⟨312505761975765987636259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1666697397204085267393381 312505761975765987636259)
      ·
        refine ⟨468758642963648981454389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312505761975765987636259 468758642963648981454389)
        ·
          refine ⟨43946122777842092011349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468758642963648981454389 43946122777842092011349)
          ·
            refine ⟨257496813151418507879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 43946122777842092011349 257496813151418507879)
            ·
              rfl

theorem cell22_60929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 9].length) (baseStart_60929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60929 prefixEnd_60929 := by exact prefixLift 60929
  have htrace : WordTrace (prefixWord ++ tailWord_60929) baseStart_60929 baseEnd_60929 := by
    simpa [prefixWord, tailWord_60929, baseEnd_60929] using wordTrace_append hprefix tailTrace_60929
  have hstable : (prefixWord ++ tailWord_60929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60929).length < 2 ^ (prefixWord ++ tailWord_60929).sum := by decide
  have hdescent : baseEnd_60929 < baseStart_60929 := by decide
  rcases family_descends (prefixWord ++ tailWord_60929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60961 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_60961 : Nat := 118140960795 + 60961 * 2 ^ 59
def prefixEnd_60961 : Nat := 4983230072969 + 3 ^ 40 * 60961 * 2
def baseEnd_60961 : Nat := 20868196119227482338101

theorem tailTrace_60961 : CollatzResearch.WordTrace tailWord_60961 prefixEnd_60961 20868196119227482338101 := by
  unfold tailWord_60961
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223430332156183155022737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1482286888104122103348491 2223430332156183155022737)
  ·
    refine ⟨1667572749117137366267053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2223430332156183155022737 1667572749117137366267053)
    ·
      refine ⟨625339780918926512350145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1667572749117137366267053 625339780918926512350145)
      ·
        refine ⟨469004835689194884262609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625339780918926512350145 469004835689194884262609)
        ·
          refine ⟨351753626766896163196957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469004835689194884262609 351753626766896163196957)
          ·
            refine ⟨131907610037586061198859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351753626766896163196957 131907610037586061198859)
            ·
              refine ⟨197861415056379091798289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131907610037586061198859 197861415056379091798289)
              ·
                refine ⟨148396061292284318848717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197861415056379091798289 148396061292284318848717)
                ·
                  refine ⟨55648522984606619568269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148396061292284318848717 55648522984606619568269)
                  ·
                    refine ⟨20868196119227482338101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55648522984606619568269 20868196119227482338101)
                    ·
                      rfl

theorem cell22_60961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_60961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60961 prefixEnd_60961 := by exact prefixLift 60961
  have htrace : WordTrace (prefixWord ++ tailWord_60961) baseStart_60961 baseEnd_60961 := by
    simpa [prefixWord, tailWord_60961, baseEnd_60961] using wordTrace_append hprefix tailTrace_60961
  have hstable : (prefixWord ++ tailWord_60961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60961).length < 2 ^ (prefixWord ++ tailWord_60961).sum := by decide
  have hdescent : baseEnd_60961 < baseStart_60961 := by decide
  rcases family_descends (prefixWord ++ tailWord_60961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60991 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 5]
def baseStart_60991 : Nat := 118140960795 + 60991 * 2 ^ 59
def prefixEnd_60991 : Nat := 4983230072969 + 3 ^ 40 * 60991 * 2
def baseEnd_60991 : Nat := 6959488577439134696003

theorem tailTrace_60991 : CollatzResearch.WordTrace tailWord_60991 prefixEnd_60991 6959488577439134696003 := by
  unfold tailWord_60991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224524522047498278614827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1483016348031665519076551 2224524522047498278614827)
  ·
    refine ⟨3336786783071247417922241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2224524522047498278614827 3336786783071247417922241)
    ·
      refine ⟨2502590087303435563441681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3336786783071247417922241 2502590087303435563441681)
      ·
        refine ⟨1876942565477576672581261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502590087303435563441681 1876942565477576672581261)
        ·
          refine ⟨703853462054091252217973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1876942565477576672581261 703853462054091252217973)
          ·
            refine ⟨65986262067571054895435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 703853462054091252217973 65986262067571054895435)
            ·
              refine ⟨98979393101356582343153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65986262067571054895435 98979393101356582343153)
              ·
                refine ⟨74234544826017436757365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98979393101356582343153 74234544826017436757365)
                ·
                  refine ⟨6959488577439134696003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74234544826017436757365 6959488577439134696003)
                  ·
                    rfl

theorem cell22_60991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].length) (baseStart_60991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_60991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_60991 prefixEnd_60991 := by exact prefixLift 60991
  have htrace : WordTrace (prefixWord ++ tailWord_60991) baseStart_60991 baseEnd_60991 := by
    simpa [prefixWord, tailWord_60991, baseEnd_60991] using wordTrace_append hprefix tailTrace_60991
  have hstable : (prefixWord ++ tailWord_60991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60991).length < 2 ^ (prefixWord ++ tailWord_60991).sum := by decide
  have hdescent : baseEnd_60991 < baseStart_60991 := by decide
  rcases family_descends (prefixWord ++ tailWord_60991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61051 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 2, 3]
def baseStart_61051 : Nat := 118140960795 + 61051 * 2 ^ 59
def prefixEnd_61051 : Nat := 4983230072969 + 3 ^ 40 * 61051 * 2
def baseEnd_61051 : Nat := 20899004958497247587825

theorem tailTrace_61051 : CollatzResearch.WordTrace tailWord_61051 prefixEnd_61051 20899004958497247587825 := by
  unfold tailWord_61051
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226712901830128525799007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1484475267886752350532671 2226712901830128525799007)
  ·
    refine ⟨3340069352745192788698511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226712901830128525799007 3340069352745192788698511)
    ·
      refine ⟨5010104029117789183047767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3340069352745192788698511 5010104029117789183047767)
      ·
        refine ⟨7515156043676683774571651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010104029117789183047767 7515156043676683774571651)
        ·
          refine ⟨11272734065515025661857477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7515156043676683774571651 11272734065515025661857477)
          ·
            refine ⟨2113637637284067311598277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11272734065515025661857477 2113637637284067311598277)
            ·
              refine ⟨396307056990762620924677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2113637637284067311598277 396307056990762620924677)
              ·
                refine ⟨74307573185767991423377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396307056990762620924677 74307573185767991423377)
                ·
                  refine ⟨55730679889325993567533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74307573185767991423377 55730679889325993567533)
                  ·
                    refine ⟨20899004958497247587825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55730679889325993567533 20899004958497247587825)
                    ·
                      rfl

theorem cell22_61051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].length) (baseStart_61051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61051 prefixEnd_61051 := by exact prefixLift 61051
  have htrace : WordTrace (prefixWord ++ tailWord_61051) baseStart_61051 baseEnd_61051 := by
    simpa [prefixWord, tailWord_61051, baseEnd_61051] using wordTrace_append hprefix tailTrace_61051
  have hstable : (prefixWord ++ tailWord_61051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61051).length < 2 ^ (prefixWord ++ tailWord_61051).sum := by decide
  have hdescent : baseEnd_61051 < baseStart_61051 := by decide
  rcases family_descends (prefixWord ++ tailWord_61051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61102 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_61102 : Nat := 118140960795 + 61102 * 2 ^ 59
def prefixEnd_61102 : Nat := 4983230072969 + 3 ^ 40 * 61102 * 2
def baseEnd_61102 : Nat := 20916463300750114562669

theorem tailTrace_61102 : CollatzResearch.WordTrace tailWord_61102 prefixEnd_61102 20916463300750114562669 := by
  unfold tailWord_61102
  simp only [CollatzResearch.WordTrace]
  refine ⟨278571628080670529488195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1485715349763576157270373 278571628080670529488195)
  ·
    refine ⟨417857442121005794232293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278571628080670529488195 417857442121005794232293)
    ·
      refine ⟨78348270397688586418555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417857442121005794232293 78348270397688586418555)
      ·
        refine ⟨117522405596532879627833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78348270397688586418555 117522405596532879627833)
        ·
          refine ⟨88141804197399659720875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117522405596532879627833 88141804197399659720875)
          ·
            refine ⟨132212706296099489581313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88141804197399659720875 132212706296099489581313)
            ·
              refine ⟨99159529722074617185985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132212706296099489581313 99159529722074617185985)
              ·
                refine ⟨74369647291555962889489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99159529722074617185985 74369647291555962889489)
                ·
                  refine ⟨55777235468666972167117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74369647291555962889489 55777235468666972167117)
                  ·
                    refine ⟨20916463300750114562669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55777235468666972167117 20916463300750114562669)
                    ·
                      rfl

theorem cell22_61102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_61102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61102 prefixEnd_61102 := by exact prefixLift 61102
  have htrace : WordTrace (prefixWord ++ tailWord_61102) baseStart_61102 baseEnd_61102 := by
    simpa [prefixWord, tailWord_61102, baseEnd_61102] using wordTrace_append hprefix tailTrace_61102
  have hstable : (prefixWord ++ tailWord_61102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61102).length < 2 ^ (prefixWord ++ tailWord_61102).sum := by decide
  have hdescent : baseEnd_61102 < baseStart_61102 := by decide
  rcases family_descends (prefixWord ++ tailWord_61102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61201 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_61201 : Nat := 118140960795 + 61201 * 2 ^ 59
def prefixEnd_61201 : Nat := 4983230072969 + 3 ^ 40 * 61201 * 2
def baseEnd_61201 : Nat := 20950353023946856337365

theorem tailTrace_61201 : CollatzResearch.WordTrace tailWord_61201 prefixEnd_61201 20950353023946856337365 := by
  unfold tailWord_61201
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232183851286704143759457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1488122567524469429172971 2232183851286704143759457)
  ·
    refine ⟨1674137888465028107819593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232183851286704143759457 1674137888465028107819593)
    ·
      refine ⟨1255603416348771080864695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1674137888465028107819593 1255603416348771080864695)
      ·
        refine ⟨1883405124523156621297043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255603416348771080864695 1883405124523156621297043)
        ·
          refine ⟨2825107686784734931945565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883405124523156621297043 2825107686784734931945565)
          ·
            refine ⟨1059415382544275599479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2825107686784734931945565 1059415382544275599479587)
            ·
              refine ⟨1589123073816413399219381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059415382544275599479587 1589123073816413399219381)
              ·
                refine ⟨148980288170288756176817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589123073816413399219381 148980288170288756176817)
                ·
                  refine ⟨111735216127716567132613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148980288170288756176817 111735216127716567132613)
                  ·
                    refine ⟨20950353023946856337365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111735216127716567132613 20950353023946856337365)
                    ·
                      rfl

theorem cell22_61201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_61201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61201 prefixEnd_61201 := by exact prefixLift 61201
  have htrace : WordTrace (prefixWord ++ tailWord_61201) baseStart_61201 baseEnd_61201 := by
    simpa [prefixWord, tailWord_61201, baseEnd_61201] using wordTrace_append hprefix tailTrace_61201
  have hstable : (prefixWord ++ tailWord_61201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61201).length < 2 ^ (prefixWord ++ tailWord_61201).sum := by decide
  have hdescent : baseEnd_61201 < baseStart_61201 := by decide
  rcases family_descends (prefixWord ++ tailWord_61201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61205 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 4]
def baseStart_61205 : Nat := 118140960795 + 61205 * 2 ^ 59
def prefixEnd_61205 : Nat := 4983230072969 + 3 ^ 40 * 61205 * 2
def baseEnd_61205 : Nat := 6983907435230726412451

theorem tailTrace_61205 : CollatzResearch.WordTrace tailWord_61205 prefixEnd_61205 6983907435230726412451 := by
  unfold tailWord_61205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232329743272212826905069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1488219828848141884603379 2232329743272212826905069)
  ·
    refine ⟨837123653727079810089401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2232329743272212826905069 837123653727079810089401)
    ·
      refine ⟨627842740295309857567051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837123653727079810089401 627842740295309857567051)
      ·
        refine ⟨941764110442964786350577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627842740295309857567051 941764110442964786350577)
        ·
          refine ⟨706323082832223589762933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941764110442964786350577 706323082832223589762933)
          ·
            refine ⟨66217789015520961540275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 706323082832223589762933 66217789015520961540275)
            ·
              refine ⟨99326683523281442310413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66217789015520961540275 99326683523281442310413)
              ·
                refine ⟨37247506321230540866405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99326683523281442310413 37247506321230540866405)
                ·
                  refine ⟨6983907435230726412451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37247506321230540866405 6983907435230726412451)
                  ·
                    rfl

theorem cell22_61205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_61205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61205 prefixEnd_61205 := by exact prefixLift 61205
  have htrace : WordTrace (prefixWord ++ tailWord_61205) baseStart_61205 baseEnd_61205 := by
    simpa [prefixWord, tailWord_61205, baseEnd_61205] using wordTrace_append hprefix tailTrace_61205
  have hstable : (prefixWord ++ tailWord_61205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61205).length < 2 ^ (prefixWord ++ tailWord_61205).sum := by decide
  have hdescent : baseEnd_61205 < baseStart_61205 := by decide
  rcases family_descends (prefixWord ++ tailWord_61205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61218 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_61218 : Nat := 118140960795 + 61218 * 2 ^ 59
def prefixEnd_61218 : Nat := 4983230072969 + 3 ^ 40 * 61218 * 2
def baseEnd_61218 : Nat := 20956172471364478662313

theorem tailTrace_61218 : CollatzResearch.WordTrace tailWord_61218 prefixEnd_61218 20956172471364478662313 := by
  unfold tailWord_61218
  simp only [CollatzResearch.WordTrace]
  refine ⟨558200973056279011782077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1488535928150077364752205 558200973056279011782077)
  ·
    refine ⟨209325364896104629418279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 558200973056279011782077 209325364896104629418279)
    ·
      refine ⟨313988047344156944127419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209325364896104629418279 313988047344156944127419)
      ·
        refine ⟨470982071016235416191129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313988047344156944127419 470982071016235416191129)
        ·
          refine ⟨353236553262176562143347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470982071016235416191129 353236553262176562143347)
          ·
            refine ⟨529854829893264843215021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353236553262176562143347 529854829893264843215021)
            ·
              refine ⟨198695561209974316205633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529854829893264843215021 198695561209974316205633)
              ·
                refine ⟨149021670907480737154225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198695561209974316205633 149021670907480737154225)
                ·
                  refine ⟨111766253180610552865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149021670907480737154225 111766253180610552865669)
                  ·
                    refine ⟨20956172471364478662313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111766253180610552865669 20956172471364478662313)
                    ·
                      rfl

theorem cell22_61218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_61218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61218 prefixEnd_61218 := by exact prefixLift 61218
  have htrace : WordTrace (prefixWord ++ tailWord_61218) baseStart_61218 baseEnd_61218 := by
    simpa [prefixWord, tailWord_61218, baseEnd_61218] using wordTrace_append hprefix tailTrace_61218
  have hstable : (prefixWord ++ tailWord_61218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61218).length < 2 ^ (prefixWord ++ tailWord_61218).sum := by decide
  have hdescent : baseEnd_61218 < baseStart_61218 := by decide
  rcases family_descends (prefixWord ++ tailWord_61218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61306 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_61306 : Nat := 118140960795 + 61306 * 2 ^ 59
def prefixEnd_61306 : Nat := 4983230072969 + 3 ^ 40 * 61306 * 2
def baseEnd_61306 : Nat := 6995432223253860820681

theorem tailTrace_61306 : CollatzResearch.WordTrace tailWord_61306 prefixEnd_61306 6995432223253860820681 := by
  unfold tailWord_61306
  simp only [CollatzResearch.WordTrace]
  refine ⟨559003378976576769082943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1490675677270871384221181 559003378976576769082943)
  ·
    refine ⟨838505068464865153624415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559003378976576769082943 838505068464865153624415)
    ·
      refine ⟨1257757602697297730436623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838505068464865153624415 1257757602697297730436623)
      ·
        refine ⟨1886636404045946595654935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257757602697297730436623 1886636404045946595654935)
        ·
          refine ⟨2829954606068919893482403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886636404045946595654935 2829954606068919893482403)
          ·
            refine ⟨4244931909103379840223605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829954606068919893482403 4244931909103379840223605)
            ·
              refine ⟨397962366478441860020963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4244931909103379840223605 397962366478441860020963)
              ·
                refine ⟨596943549717662790031445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397962366478441860020963 596943549717662790031445)
                ·
                  refine ⟨6995432223253860820681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 596943549717662790031445 6995432223253860820681)
                  ·
                    rfl

theorem cell22_61306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_61306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61306 prefixEnd_61306 := by exact prefixLift 61306
  have htrace : WordTrace (prefixWord ++ tailWord_61306) baseStart_61306 baseEnd_61306 := by
    simpa [prefixWord, tailWord_61306, baseEnd_61306] using wordTrace_append hprefix tailTrace_61306
  have hstable : (prefixWord ++ tailWord_61306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61306).length < 2 ^ (prefixWord ++ tailWord_61306).sum := by decide
  have hdescent : baseEnd_61306 < baseStart_61306 := by decide
  rcases family_descends (prefixWord ++ tailWord_61306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61340 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_61340 : Nat := 118140960795 + 61340 * 2 ^ 59
def prefixEnd_61340 : Nat := 4983230072969 + 3 ^ 40 * 61340 * 2
def baseEnd_61340 : Nat := 6999311854865609037313

theorem tailTrace_61340 : CollatzResearch.WordTrace tailWord_61340 prefixEnd_61340 6999311854865609037313 := by
  unfold tailWord_61340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118626798891565441534737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1491502398522087255379649 1118626798891565441534737)
  ·
    refine ⟨838970099168674081151053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1118626798891565441534737 838970099168674081151053)
    ·
      refine ⟨314613787188252780431645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 838970099168674081151053 314613787188252780431645)
      ·
        refine ⟨117980170195594792661867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314613787188252780431645 117980170195594792661867)
        ·
          refine ⟨176970255293392188992801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117980170195594792661867 176970255293392188992801)
          ·
            refine ⟨132727691470044141744601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176970255293392188992801 132727691470044141744601)
            ·
              refine ⟨99545768602533106308451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132727691470044141744601 99545768602533106308451)
              ·
                refine ⟨149318652903799659462677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99545768602533106308451 149318652903799659462677)
                ·
                  refine ⟨6999311854865609037313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149318652903799659462677 6999311854865609037313)
                  ·
                    rfl

theorem cell22_61340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_61340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61340 prefixEnd_61340 := by exact prefixLift 61340
  have htrace : WordTrace (prefixWord ++ tailWord_61340) baseStart_61340 baseEnd_61340 := by
    simpa [prefixWord, tailWord_61340, baseEnd_61340] using wordTrace_append hprefix tailTrace_61340
  have hstable : (prefixWord ++ tailWord_61340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61340).length < 2 ^ (prefixWord ++ tailWord_61340).sum := by decide
  have hdescent : baseEnd_61340 < baseStart_61340 := by decide
  rcases family_descends (prefixWord ++ tailWord_61340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61490 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_61490 : Nat := 118140960795 + 61490 * 2 ^ 59
def prefixEnd_61490 : Nat := 4983230072969 + 3 ^ 40 * 61490 * 2
def baseEnd_61490 : Nat := 21049283630046435861479

theorem tailTrace_61490 : CollatzResearch.WordTrace tailWord_61490 prefixEnd_61490 21049283630046435861479 := by
  unfold tailWord_61490
  simp only [CollatzResearch.WordTrace]
  refine ⟨560681136809926625257481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1495149698159804334019949 560681136809926625257481)
  ·
    refine ⟨420510852607444968943111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 560681136809926625257481 420510852607444968943111)
    ·
      refine ⟨630766278911167453414667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420510852607444968943111 630766278911167453414667)
      ·
        refine ⟨946149418366751180122001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630766278911167453414667 946149418366751180122001)
        ·
          refine ⟨709612063775063385091501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946149418366751180122001 709612063775063385091501)
          ·
            refine ⟨266104523915648769409313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709612063775063385091501 266104523915648769409313)
            ·
              refine ⟨199578392936736577056985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266104523915648769409313 199578392936736577056985)
              ·
                refine ⟨149683794702552432792739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199578392936736577056985 149683794702552432792739)
                ·
                  refine ⟨224525692053828649189109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149683794702552432792739 224525692053828649189109)
                  ·
                    refine ⟨21049283630046435861479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224525692053828649189109 21049283630046435861479)
                    ·
                      rfl

theorem cell22_61490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_61490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61490 prefixEnd_61490 := by exact prefixLift 61490
  have htrace : WordTrace (prefixWord ++ tailWord_61490) baseStart_61490 baseEnd_61490 := by
    simpa [prefixWord, tailWord_61490, baseEnd_61490] using wordTrace_append hprefix tailTrace_61490
  have hstable : (prefixWord ++ tailWord_61490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61490).length < 2 ^ (prefixWord ++ tailWord_61490).sum := by decide
  have hdescent : baseEnd_61490 < baseStart_61490 := by decide
  rcases family_descends (prefixWord ++ tailWord_61490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61535 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 5, 3]
def baseStart_61535 : Nat := 118140960795 + 61535 * 2 ^ 59
def prefixEnd_61535 : Nat := 4983230072969 + 3 ^ 40 * 61535 * 2
def baseEnd_61535 : Nat := 21064688049681318486341

theorem tailTrace_61535 : CollatzResearch.WordTrace tailWord_61535 prefixEnd_61535 21064688049681318486341 := by
  unfold tailWord_61535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244365832076679186418059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496243888051119457612039 2244365832076679186418059)
  ·
    refine ⟨3366548748115018779627089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244365832076679186418059 3366548748115018779627089)
    ·
      refine ⟨2524911561086264084720317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366548748115018779627089 2524911561086264084720317)
      ·
        refine ⟨946841835407349031770119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524911561086264084720317 946841835407349031770119)
        ·
          refine ⟨1420262753111023547655179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946841835407349031770119 1420262753111023547655179)
          ·
            refine ⟨2130394129666535321482769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420262753111023547655179 2130394129666535321482769)
            ·
              refine ⟨1597795597249901491112077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130394129666535321482769 1597795597249901491112077)
              ·
                refine ⟨599173348968713059167029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597795597249901491112077 599173348968713059167029)
                ·
                  refine ⟨56172501465816849296909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599173348968713059167029 56172501465816849296909)
                  ·
                    refine ⟨21064688049681318486341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56172501465816849296909 21064688049681318486341)
                    ·
                      rfl

theorem cell22_61535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_61535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61535 prefixEnd_61535 := by exact prefixLift 61535
  have htrace : WordTrace (prefixWord ++ tailWord_61535) baseStart_61535 baseEnd_61535 := by
    simpa [prefixWord, tailWord_61535, baseEnd_61535] using wordTrace_append hprefix tailTrace_61535
  have hstable : (prefixWord ++ tailWord_61535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61535).length < 2 ^ (prefixWord ++ tailWord_61535).sum := by decide
  have hdescent : baseEnd_61535 < baseStart_61535 := by decide
  rcases family_descends (prefixWord ++ tailWord_61535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61565 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 7]
def baseStart_61565 : Nat := 118140960795 + 61565 * 2 ^ 59
def prefixEnd_61565 : Nat := 4983230072969 + 3 ^ 40 * 61565 * 2
def baseEnd_61565 : Nat := 7024985887590413412083

theorem tailTrace_61565 : CollatzResearch.WordTrace tailWord_61565 prefixEnd_61565 7024985887590413412083 := by
  unfold tailWord_61565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245460021967994310010149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496973347978662873340099 2245460021967994310010149)
  ·
    refine ⟨421023754118998933126903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2245460021967994310010149 421023754118998933126903)
    ·
      refine ⟨631535631178498399690355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421023754118998933126903 631535631178498399690355)
      ·
        refine ⟨947303446767747599535533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631535631178498399690355 947303446767747599535533)
        ·
          refine ⟨355238792537905349825825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947303446767747599535533 355238792537905349825825)
          ·
            refine ⟨266429094403429012369369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355238792537905349825825 266429094403429012369369)
            ·
              refine ⟨199821820802571759277027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266429094403429012369369 199821820802571759277027)
              ·
                refine ⟨299732731203857638915541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199821820802571759277027 299732731203857638915541)
                ·
                  refine ⟨7024985887590413412083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 299732731203857638915541 7024985887590413412083)
                  ·
                    rfl

theorem cell22_61565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_61565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61565 prefixEnd_61565 := by exact prefixLift 61565
  have htrace : WordTrace (prefixWord ++ tailWord_61565) baseStart_61565 baseEnd_61565 := by
    simpa [prefixWord, tailWord_61565, baseEnd_61565] using wordTrace_append hprefix tailTrace_61565
  have hstable : (prefixWord ++ tailWord_61565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61565).length < 2 ^ (prefixWord ++ tailWord_61565).sum := by decide
  have hdescent : baseEnd_61565 < baseStart_61565 := by decide
  rcases family_descends (prefixWord ++ tailWord_61565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61590 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_61590 : Nat := 118140960795 + 61590 * 2 ^ 59
def prefixEnd_61590 : Nat := 4983230072969 + 3 ^ 40 * 61590 * 2
def baseEnd_61590 : Nat := 21083515673679508361173

theorem tailTrace_61590 : CollatzResearch.WordTrace tailWord_61590 prefixEnd_61590 21083515673679508361173 := by
  unfold tailWord_61590
  simp only [CollatzResearch.WordTrace]
  refine ⟨140398240429838973729389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1497581231251615719780149 140398240429838973729389)
  ·
    refine ⟨52649340161189615148521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140398240429838973729389 52649340161189615148521)
    ·
      refine ⟨39487005120892211361391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52649340161189615148521 39487005120892211361391)
      ·
        refine ⟨59230507681338317042087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39487005120892211361391 59230507681338317042087)
        ·
          refine ⟨88845761522007475563131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59230507681338317042087 88845761522007475563131)
          ·
            refine ⟨133268642283011213344697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88845761522007475563131 133268642283011213344697)
            ·
              refine ⟨99951481712258410008523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133268642283011213344697 99951481712258410008523)
              ·
                refine ⟨149927222568387615012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99951481712258410008523 149927222568387615012785)
                ·
                  refine ⟨112445416926290711259589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149927222568387615012785 112445416926290711259589)
                  ·
                    refine ⟨21083515673679508361173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112445416926290711259589 21083515673679508361173)
                    ·
                      rfl

theorem cell22_61590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_61590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61590 prefixEnd_61590 := by exact prefixLift 61590
  have htrace : WordTrace (prefixWord ++ tailWord_61590) baseStart_61590 baseEnd_61590 := by
    simpa [prefixWord, tailWord_61590, baseEnd_61590] using wordTrace_append hprefix tailTrace_61590
  have hstable : (prefixWord ++ tailWord_61590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61590).length < 2 ^ (prefixWord ++ tailWord_61590).sum := by decide
  have hdescent : baseEnd_61590 < baseStart_61590 := by decide
  rcases family_descends (prefixWord ++ tailWord_61590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61625 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_61625 : Nat := 118140960795 + 61625 * 2 ^ 59
def prefixEnd_61625 : Nat := 4983230072969 + 3 ^ 40 * 61625 * 2
def baseEnd_61625 : Nat := 21095496888951083736065

theorem tailTrace_61625 : CollatzResearch.WordTrace tailWord_61625 prefixEnd_61625 21095496888951083736065 := by
  unfold tailWord_61625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247648401750624557194329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1498432267833749704796219 2247648401750624557194329)
  ·
    refine ⟨1685736301312968417895747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247648401750624557194329 1685736301312968417895747)
    ·
      refine ⟨2528604451969452626843621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685736301312968417895747 2528604451969452626843621)
      ·
        refine ⟨474113334744272367533179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2528604451969452626843621 474113334744272367533179)
        ·
          refine ⟨711170002116408551299769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474113334744272367533179 711170002116408551299769)
          ·
            refine ⟨533377501587306413474827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711170002116408551299769 533377501587306413474827)
            ·
              refine ⟨800066252380959620212241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533377501587306413474827 800066252380959620212241)
              ·
                refine ⟨600049689285719715159181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800066252380959620212241 600049689285719715159181)
                ·
                  refine ⟨225018633482144893184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600049689285719715159181 225018633482144893184693)
                  ·
                    refine ⟨21095496888951083736065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225018633482144893184693 21095496888951083736065)
                    ·
                      rfl

theorem cell22_61625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_61625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61625 prefixEnd_61625 := by exact prefixLift 61625
  have htrace : WordTrace (prefixWord ++ tailWord_61625) baseStart_61625 baseEnd_61625 := by
    simpa [prefixWord, tailWord_61625, baseEnd_61625] using wordTrace_append hprefix tailTrace_61625
  have hstable : (prefixWord ++ tailWord_61625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61625).length < 2 ^ (prefixWord ++ tailWord_61625).sum := by decide
  have hdescent : baseEnd_61625 < baseStart_61625 := by decide
  rcases family_descends (prefixWord ++ tailWord_61625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61627 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 4]
def baseStart_61627 : Nat := 118140960795 + 61627 * 2 ^ 59
def prefixEnd_61627 : Nat := 4983230072969 + 3 ^ 40 * 61627 * 2
def baseEnd_61627 : Nat := 7032060509941248395353

theorem tailTrace_61627 : CollatzResearch.WordTrace tailWord_61627 prefixEnd_61627 7032060509941248395353 := by
  unfold tailWord_61627
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247721347743378898767135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1498480898495585932511423 2247721347743378898767135)
  ·
    refine ⟨3371582021615068348150703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247721347743378898767135 3371582021615068348150703)
    ·
      refine ⟨5057373032422602522226055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371582021615068348150703 5057373032422602522226055)
      ·
        refine ⟨7586059548633903783339083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057373032422602522226055 7586059548633903783339083)
        ·
          refine ⟨11379089322950855675008625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586059548633903783339083 11379089322950855675008625)
          ·
            refine ⟨8534316992213141756256469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379089322950855675008625 8534316992213141756256469)
            ·
              refine ⟨200023054504995509912261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8534316992213141756256469 200023054504995509912261)
              ·
                refine ⟨37504322719686658108549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200023054504995509912261 37504322719686658108549)
                ·
                  refine ⟨7032060509941248395353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37504322719686658108549 7032060509941248395353)
                  ·
                    rfl

theorem cell22_61627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 4].length) (baseStart_61627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61627 prefixEnd_61627 := by exact prefixLift 61627
  have htrace : WordTrace (prefixWord ++ tailWord_61627) baseStart_61627 baseEnd_61627 := by
    simpa [prefixWord, tailWord_61627, baseEnd_61627] using wordTrace_append hprefix tailTrace_61627
  have hstable : (prefixWord ++ tailWord_61627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61627).length < 2 ^ (prefixWord ++ tailWord_61627).sum := by decide
  have hdescent : baseEnd_61627 < baseStart_61627 := by decide
  rcases family_descends (prefixWord ++ tailWord_61627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61640 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_61640 : Nat := 118140960795 + 61640 * 2 ^ 59
def prefixEnd_61640 : Nat := 4983230072969 + 3 ^ 40 * 61640 * 2
def baseEnd_61640 : Nat := 21100631695496044611019

theorem tailTrace_61640 : CollatzResearch.WordTrace tailWord_61640 prefixEnd_61640 21100631695496044611019 := by
  unfold tailWord_61640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124097748348141059495187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1498796997797521412660249 1124097748348141059495187)
  ·
    refine ⟨1686146622522211589242781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124097748348141059495187 1686146622522211589242781)
    ·
      refine ⟨632304983445829345966043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1686146622522211589242781 632304983445829345966043)
      ·
        refine ⟨948457475168744018949065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632304983445829345966043 948457475168744018949065)
        ·
          refine ⟨711343106376558014211799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948457475168744018949065 711343106376558014211799)
          ·
            refine ⟨1067014659564837021317699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711343106376558014211799 1067014659564837021317699)
            ·
              refine ⟨1600521989347255531976549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067014659564837021317699 1600521989347255531976549)
              ·
                refine ⟨300097873002610412245603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1600521989347255531976549 300097873002610412245603)
                ·
                  refine ⟨450146809503915618368405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300097873002610412245603 450146809503915618368405)
                  ·
                    refine ⟨21100631695496044611019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 450146809503915618368405 21100631695496044611019)
                    ·
                      rfl

theorem cell22_61640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_61640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61640 prefixEnd_61640 := by exact prefixLift 61640
  have htrace : WordTrace (prefixWord ++ tailWord_61640) baseStart_61640 baseEnd_61640 := by
    simpa [prefixWord, tailWord_61640, baseEnd_61640] using wordTrace_append hprefix tailTrace_61640
  have hstable : (prefixWord ++ tailWord_61640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61640).length < 2 ^ (prefixWord ++ tailWord_61640).sum := by decide
  have hdescent : baseEnd_61640 < baseStart_61640 := by decide
  rcases family_descends (prefixWord ++ tailWord_61640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61642 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_61642 : Nat := 118140960795 + 61642 * 2 ^ 59
def prefixEnd_61642 : Nat := 4983230072969 + 3 ^ 40 * 61642 * 2
def baseEnd_61642 : Nat := 21101316336368706061013

theorem tailTrace_61642 : CollatzResearch.WordTrace tailWord_61642 prefixEnd_61642 21101316336368706061013 := by
  unfold tailWord_61642
  simp only [CollatzResearch.WordTrace]
  refine ⟨562067110672259115140795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1498845628459357640375453 562067110672259115140795)
  ·
    refine ⟨843100666008388672711193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 562067110672259115140795 843100666008388672711193)
    ·
      refine ⟨632325499506291504533395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843100666008388672711193 632325499506291504533395)
      ·
        refine ⟨948488249259437256800093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632325499506291504533395 948488249259437256800093)
        ·
          refine ⟨355683093472288971300035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 948488249259437256800093 355683093472288971300035)
          ·
            refine ⟨533524640208433456950053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355683093472288971300035 533524640208433456950053)
            ·
              refine ⟨100035870039081273178135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533524640208433456950053 100035870039081273178135)
              ·
                refine ⟨150053805058621909767203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100035870039081273178135 150053805058621909767203)
                ·
                  refine ⟨225080707587932864650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150053805058621909767203 225080707587932864650805)
                  ·
                    refine ⟨21101316336368706061013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225080707587932864650805 21101316336368706061013)
                    ·
                      rfl

theorem cell22_61642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_61642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61642 prefixEnd_61642 := by exact prefixLift 61642
  have htrace : WordTrace (prefixWord ++ tailWord_61642) baseStart_61642 baseEnd_61642 := by
    simpa [prefixWord, tailWord_61642, baseEnd_61642] using wordTrace_append hprefix tailTrace_61642
  have hstable : (prefixWord ++ tailWord_61642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61642).length < 2 ^ (prefixWord ++ tailWord_61642).sum := by decide
  have hdescent : baseEnd_61642 < baseStart_61642 := by decide
  rcases family_descends (prefixWord ++ tailWord_61642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61644 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_61644 : Nat := 118140960795 + 61644 * 2 ^ 59
def prefixEnd_61644 : Nat := 4983230072969 + 3 ^ 40 * 61644 * 2
def baseEnd_61644 : Nat := 7034000325747122503669

theorem tailTrace_61644 : CollatzResearch.WordTrace tailWord_61644 prefixEnd_61644 7034000325747122503669 := by
  unfold tailWord_61644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124170694340895401067993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1498894259121193868090657 1124170694340895401067993)
  ·
    refine ⟨843128020755671550800995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124170694340895401067993 843128020755671550800995)
    ·
      refine ⟨1264692031133507326201493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843128020755671550800995 1264692031133507326201493)
      ·
        refine ⟨59282438959383155915695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1264692031133507326201493 59282438959383155915695)
        ·
          refine ⟨88923658439074733873543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59282438959383155915695 88923658439074733873543)
          ·
            refine ⟨133385487658612100810315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88923658439074733873543 133385487658612100810315)
            ·
              refine ⟨200078231487918151215473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133385487658612100810315 200078231487918151215473)
              ·
                refine ⟨150058673615938613411605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200078231487918151215473 150058673615938613411605)
                ·
                  refine ⟨7034000325747122503669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150058673615938613411605 7034000325747122503669)
                  ·
                    rfl

theorem cell22_61644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_61644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61644 prefixEnd_61644 := by exact prefixLift 61644
  have htrace : WordTrace (prefixWord ++ tailWord_61644) baseStart_61644 baseEnd_61644 := by
    simpa [prefixWord, tailWord_61644, baseEnd_61644] using wordTrace_append hprefix tailTrace_61644
  have hstable : (prefixWord ++ tailWord_61644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61644).length < 2 ^ (prefixWord ++ tailWord_61644).sum := by decide
  have hdescent : baseEnd_61644 < baseStart_61644 := by decide
  rcases family_descends (prefixWord ++ tailWord_61644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61657 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_61657 : Nat := 118140960795 + 61657 * 2 ^ 59
def prefixEnd_61657 : Nat := 4983230072969 + 3 ^ 40 * 61657 * 2
def baseEnd_61657 : Nat := 21106451142913666935967

theorem tailTrace_61657 : CollatzResearch.WordTrace tailWord_61657 prefixEnd_61657 21106451142913666935967 := by
  unfold tailWord_61657
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248815537634694022359225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1499210358423129348239483 2248815537634694022359225)
  ·
    refine ⟨1686611653226020516769419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2248815537634694022359225 1686611653226020516769419)
    ·
      refine ⟨2529917479839030775154129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686611653226020516769419 2529917479839030775154129)
      ·
        refine ⟨1897438109879273081365597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529917479839030775154129 1897438109879273081365597)
        ·
          refine ⟨711539291204727405512099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1897438109879273081365597 711539291204727405512099)
          ·
            refine ⟨1067308936807091108268149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711539291204727405512099 1067308936807091108268149)
            ·
              refine ⟨100060212825664791400139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1067308936807091108268149 100060212825664791400139)
              ·
                refine ⟨150090319238497187100209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100060212825664791400139 150090319238497187100209)
                ·
                  refine ⟨112567739428872890325157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150090319238497187100209 112567739428872890325157)
                  ·
                    refine ⟨21106451142913666935967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112567739428872890325157 21106451142913666935967)
                    ·
                      rfl

theorem cell22_61657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_61657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61657 prefixEnd_61657 := by exact prefixLift 61657
  have htrace : WordTrace (prefixWord ++ tailWord_61657) baseStart_61657 baseEnd_61657 := by
    simpa [prefixWord, tailWord_61657, baseEnd_61657] using wordTrace_append hprefix tailTrace_61657
  have hstable : (prefixWord ++ tailWord_61657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61657).length < 2 ^ (prefixWord ++ tailWord_61657).sum := by decide
  have hdescent : baseEnd_61657 < baseStart_61657 := by decide
  rcases family_descends (prefixWord ++ tailWord_61657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61661 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 4]
def baseStart_61661 : Nat := 118140960795 + 61661 * 2 ^ 59
def prefixEnd_61661 : Nat := 4983230072969 + 3 ^ 40 * 61661 * 2
def baseEnd_61661 : Nat := 7035940141552996611985

theorem tailTrace_61661 : CollatzResearch.WordTrace tailWord_61661 prefixEnd_61661 7035940141552996611985 := by
  unfold tailWord_61661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248961429620202705504837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1499307619746801803669891 2248961429620202705504837)
  ·
    refine ⟨421680268053788007282157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2248961429620202705504837 421680268053788007282157)
    ·
      refine ⟨158130100520170502730809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421680268053788007282157 158130100520170502730809)
      ·
        refine ⟨118597575390127877048107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158130100520170502730809 118597575390127877048107)
        ·
          refine ⟨177896363085191815572161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118597575390127877048107 177896363085191815572161)
          ·
            refine ⟨133422272313893861679121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177896363085191815572161 133422272313893861679121)
            ·
              refine ⟨100066704235420396259341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133422272313893861679121 100066704235420396259341)
              ·
                refine ⟨37525014088282648597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100066704235420396259341 37525014088282648597253)
                ·
                  refine ⟨7035940141552996611985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37525014088282648597253 7035940141552996611985)
                  ·
                    rfl

theorem cell22_61661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_61661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61661 prefixEnd_61661 := by exact prefixLift 61661
  have htrace : WordTrace (prefixWord ++ tailWord_61661) baseStart_61661 baseEnd_61661 := by
    simpa [prefixWord, tailWord_61661, baseEnd_61661] using wordTrace_append hprefix tailTrace_61661
  have hstable : (prefixWord ++ tailWord_61661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61661).length < 2 ^ (prefixWord ++ tailWord_61661).sum := by decide
  have hdescent : baseEnd_61661 < baseStart_61661 := by decide
  rcases family_descends (prefixWord ++ tailWord_61661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61704 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_61704 : Nat := 118140960795 + 61704 * 2 ^ 59
def prefixEnd_61704 : Nat := 4983230072969 + 3 ^ 40 * 61704 * 2
def baseEnd_61704 : Nat := 21122540203421211010823

theorem tailTrace_61704 : CollatzResearch.WordTrace tailWord_61704 prefixEnd_61704 21122540203421211010823 := by
  unfold tailWord_61704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125264884232210524660083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1500353178976280699546777 1125264884232210524660083)
  ·
    refine ⟨1687897326348315786990125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125264884232210524660083 1687897326348315786990125)
    ·
      refine ⟨632961497380618420121297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1687897326348315786990125 632961497380618420121297)
      ·
        refine ⟨474721123035463815090973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632961497380618420121297 474721123035463815090973)
        ·
          refine ⟨178020421138298930659115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474721123035463815090973 178020421138298930659115)
          ·
            refine ⟨267030631707448395988673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178020421138298930659115 267030631707448395988673)
            ·
              refine ⟨200272973780586296991505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267030631707448395988673 200272973780586296991505)
              ·
                refine ⟨150204730335439722743629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200272973780586296991505 150204730335439722743629)
                ·
                  refine ⟨56326773875789896028861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150204730335439722743629 56326773875789896028861)
                  ·
                    refine ⟨21122540203421211010823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56326773875789896028861 21122540203421211010823)
                    ·
                      rfl

theorem cell22_61704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_61704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61704 prefixEnd_61704 := by exact prefixLift 61704
  have htrace : WordTrace (prefixWord ++ tailWord_61704) baseStart_61704 baseEnd_61704 := by
    simpa [prefixWord, tailWord_61704, baseEnd_61704] using wordTrace_append hprefix tailTrace_61704
  have hstable : (prefixWord ++ tailWord_61704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61704).length < 2 ^ (prefixWord ++ tailWord_61704).sum := by decide
  have hdescent : baseEnd_61704 < baseStart_61704 := by decide
  rcases family_descends (prefixWord ++ tailWord_61704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_61715 : Nat := 118140960795 + 61715 * 2 ^ 59
def prefixEnd_61715 : Nat := 4983230072969 + 3 ^ 40 * 61715 * 2
def baseEnd_61715 : Nat := 21126305728220848985789

theorem tailTrace_61715 : CollatzResearch.WordTrace tailWord_61715 prefixEnd_61715 21126305728220848985789 := by
  unfold tailWord_61715
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250930971424569927970599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1500620647616379951980399 2250930971424569927970599)
  ·
    refine ⟨3376396457136854891955899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250930971424569927970599 3376396457136854891955899)
    ·
      refine ⟨5064594685705282337933849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376396457136854891955899 5064594685705282337933849)
      ·
        refine ⟨3798446014278961753450387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064594685705282337933849 3798446014278961753450387)
        ·
          refine ⟨5697669021418442630175581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798446014278961753450387 5697669021418442630175581)
          ·
            refine ⟨2136625883031915986315843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5697669021418442630175581 2136625883031915986315843)
            ·
              refine ⟨3204938824547873979473765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136625883031915986315843 3204938824547873979473765)
              ·
                refine ⟨600926029602726371151331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3204938824547873979473765 600926029602726371151331)
                ·
                  refine ⟨901389044404089556726997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600926029602726371151331 901389044404089556726997)
                  ·
                    refine ⟨21126305728220848985789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 901389044404089556726997 21126305728220848985789)
                    ·
                      rfl

theorem cell22_61715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_61715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61715 prefixEnd_61715 := by exact prefixLift 61715
  have htrace : WordTrace (prefixWord ++ tailWord_61715) baseStart_61715 baseEnd_61715 := by
    simpa [prefixWord, tailWord_61715, baseEnd_61715] using wordTrace_append hprefix tailTrace_61715
  have hstable : (prefixWord ++ tailWord_61715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61715).length < 2 ^ (prefixWord ++ tailWord_61715).sum := by decide
  have hdescent : baseEnd_61715 < baseStart_61715 := by decide
  rcases family_descends (prefixWord ++ tailWord_61715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61738 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_61738 : Nat := 118140960795 + 61738 * 2 ^ 59
def prefixEnd_61738 : Nat := 4983230072969 + 3 ^ 40 * 61738 * 2
def baseEnd_61738 : Nat := 21134179098256455660719

theorem tailTrace_61738 : CollatzResearch.WordTrace tailWord_61738 prefixEnd_61738 21134179098256455660719 := by
  unfold tailWord_61738
  simp only [CollatzResearch.WordTrace]
  refine ⟨562942462585311214014467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1501179900227496570705245 562942462585311214014467)
  ·
    refine ⟨844413693877966821021701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 562942462585311214014467 844413693877966821021701)
    ·
      refine ⟨158327567602118778941569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 844413693877966821021701 158327567602118778941569)
      ·
        refine ⟨118745675701589084206177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158327567602118778941569 118745675701589084206177)
        ·
          refine ⟨89059256776191813154633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118745675701589084206177 89059256776191813154633)
          ·
            refine ⟨66794442582143859865975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89059256776191813154633 66794442582143859865975)
            ·
              refine ⟨100191663873215789798963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66794442582143859865975 100191663873215789798963)
              ·
                refine ⟨150287495809823684698445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100191663873215789798963 150287495809823684698445)
                ·
                  refine ⟨56357810928683881761917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150287495809823684698445 56357810928683881761917)
                  ·
                    refine ⟨21134179098256455660719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56357810928683881761917 21134179098256455660719)
                    ·
                      rfl

theorem cell22_61738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_61738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61738 prefixEnd_61738 := by exact prefixLift 61738
  have htrace : WordTrace (prefixWord ++ tailWord_61738) baseStart_61738 baseEnd_61738 := by
    simpa [prefixWord, tailWord_61738, baseEnd_61738] using wordTrace_append hprefix tailTrace_61738
  have hstable : (prefixWord ++ tailWord_61738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61738).length < 2 ^ (prefixWord ++ tailWord_61738).sum := by decide
  have hdescent : baseEnd_61738 < baseStart_61738 := by decide
  rcases family_descends (prefixWord ++ tailWord_61738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61747 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_61747 : Nat := 118140960795 + 61747 * 2 ^ 59
def prefixEnd_61747 : Nat := 4983230072969 + 3 ^ 40 * 61747 * 2
def baseEnd_61747 : Nat := 21137259982183432185691

theorem tailTrace_61747 : CollatzResearch.WordTrace tailWord_61747 prefixEnd_61747 21137259982183432185691 := by
  unfold tailWord_61747
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252098107308639393135495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501398738205759595423663 2252098107308639393135495)
  ·
    refine ⟨3378147160962959089703243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252098107308639393135495 3378147160962959089703243)
    ·
      refine ⟨5067220741444438634554865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3378147160962959089703243 5067220741444438634554865)
      ·
        refine ⟨3800415556083328975916149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5067220741444438634554865 3800415556083328975916149)
        ·
          refine ⟨356288958382812091492139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3800415556083328975916149 356288958382812091492139)
          ·
            refine ⟨534433437574218137238209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356288958382812091492139 534433437574218137238209)
            ·
              refine ⟨400825078180663602928657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534433437574218137238209 400825078180663602928657)
              ·
                refine ⟨300618808635497702196493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400825078180663602928657 300618808635497702196493)
                ·
                  refine ⟨112732053238311638323685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300618808635497702196493 112732053238311638323685)
                  ·
                    refine ⟨21137259982183432185691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112732053238311638323685 21137259982183432185691)
                    ·
                      rfl

theorem cell22_61747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_61747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61747 prefixEnd_61747 := by exact prefixLift 61747
  have htrace : WordTrace (prefixWord ++ tailWord_61747) baseStart_61747 baseEnd_61747 := by
    simpa [prefixWord, tailWord_61747, baseEnd_61747] using wordTrace_append hprefix tailTrace_61747
  have hstable : (prefixWord ++ tailWord_61747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61747).length < 2 ^ (prefixWord ++ tailWord_61747).sum := by decide
  have hdescent : baseEnd_61747 < baseStart_61747 := by decide
  rcases family_descends (prefixWord ++ tailWord_61747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61777 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_61777 : Nat := 118140960795 + 61777 * 2 ^ 59
def prefixEnd_61777 : Nat := 4983230072969 + 3 ^ 40 * 61777 * 2
def baseEnd_61777 : Nat := 21147529595273353935599

theorem tailTrace_61777 : CollatzResearch.WordTrace tailWord_61777 prefixEnd_61777 21147529595273353935599 := by
  unfold tailWord_61777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253192297199954516727585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1502128198133303011151723 2253192297199954516727585)
  ·
    refine ⟨1689894222899965887545689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2253192297199954516727585 1689894222899965887545689)
    ·
      refine ⟨1267420667174974415659267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689894222899965887545689 1267420667174974415659267)
      ·
        refine ⟨1901131000762461623488901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267420667174974415659267 1901131000762461623488901)
        ·
          refine ⟨356462062642961554404169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1901131000762461623488901 356462062642961554404169)
          ·
            refine ⟨267346546982221165803127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356462062642961554404169 267346546982221165803127)
            ·
              refine ⟨401019820473331748704691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267346546982221165803127 401019820473331748704691)
              ·
                refine ⟨601529730709997623057037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401019820473331748704691 601529730709997623057037)
                ·
                  refine ⟨225573649016249108646389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601529730709997623057037 225573649016249108646389)
                  ·
                    refine ⟨21147529595273353935599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225573649016249108646389 21147529595273353935599)
                    ·
                      rfl

theorem cell22_61777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_61777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61777 prefixEnd_61777 := by exact prefixLift 61777
  have htrace : WordTrace (prefixWord ++ tailWord_61777) baseStart_61777 baseEnd_61777 := by
    simpa [prefixWord, tailWord_61777, baseEnd_61777] using wordTrace_append hprefix tailTrace_61777
  have hstable : (prefixWord ++ tailWord_61777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61777).length < 2 ^ (prefixWord ++ tailWord_61777).sum := by decide
  have hdescent : baseEnd_61777 < baseStart_61777 := by decide
  rcases family_descends (prefixWord ++ tailWord_61777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61856 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_61856 : Nat := 118140960795 + 61856 * 2 ^ 59
def prefixEnd_61856 : Nat := 4983230072969 + 3 ^ 40 * 61856 * 2
def baseEnd_61856 : Nat := 21174572909743481210357

theorem tailTrace_61856 : CollatzResearch.WordTrace tailWord_61856 prefixEnd_61856 21174572909743481210357 := by
  unfold tailWord_61856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128036831956875504426711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1504049109275834005902281 1128036831956875504426711)
  ·
    refine ⟨1692055247935313256640067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128036831956875504426711 1692055247935313256640067)
    ·
      refine ⟨2538082871902969884960101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692055247935313256640067 2538082871902969884960101)
      ·
        refine ⟨475890538481806853430019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2538082871902969884960101 475890538481806853430019)
        ·
          refine ⟨713835807722710280145029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475890538481806853430019 713835807722710280145029)
          ·
            refine ⟨133844213948008177527193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 713835807722710280145029 133844213948008177527193)
            ·
              refine ⟨100383160461006133145395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133844213948008177527193 100383160461006133145395)
              ·
                refine ⟨150574740691509199718093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100383160461006133145395 150574740691509199718093)
                ·
                  refine ⟨56465527759315949894285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150574740691509199718093 56465527759315949894285)
                  ·
                    refine ⟨21174572909743481210357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56465527759315949894285 21174572909743481210357)
                    ·
                      rfl

theorem cell22_61856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_61856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61856 prefixEnd_61856 := by exact prefixLift 61856
  have htrace : WordTrace (prefixWord ++ tailWord_61856) baseStart_61856 baseEnd_61856 := by
    simpa [prefixWord, tailWord_61856, baseEnd_61856] using wordTrace_append hprefix tailTrace_61856
  have hstable : (prefixWord ++ tailWord_61856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61856).length < 2 ^ (prefixWord ++ tailWord_61856).sum := by decide
  have hdescent : baseEnd_61856 < baseStart_61856 := by decide
  rcases family_descends (prefixWord ++ tailWord_61856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61882 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_61882 : Nat := 118140960795 + 61882 * 2 ^ 59
def prefixEnd_61882 : Nat := 4983230072969 + 3 ^ 40 * 61882 * 2
def baseEnd_61882 : Nat := 21183473241088080060277

theorem tailTrace_61882 : CollatzResearch.WordTrace tailWord_61882 prefixEnd_61882 21183473241088080060277 := by
  unfold tailWord_61882
  simp only [CollatzResearch.WordTrace]
  refine ⟨564255490454889362324975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1504681307879704966199933 564255490454889362324975)
  ·
    refine ⟨846383235682334043487463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564255490454889362324975 846383235682334043487463)
    ·
      refine ⟨1269574853523501065231195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846383235682334043487463 1269574853523501065231195)
      ·
        refine ⟨1904362280285251597846793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269574853523501065231195 1904362280285251597846793)
        ·
          refine ⟨1428271710213938698385095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904362280285251597846793 1428271710213938698385095)
          ·
            refine ⟨2142407565320908047577643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428271710213938698385095 2142407565320908047577643)
            ·
              refine ⟨3213611347981362071366465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142407565320908047577643 3213611347981362071366465)
              ·
                refine ⟨2410208510986021553524849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213611347981362071366465 2410208510986021553524849)
                ·
                  refine ⟨1807656383239516165143637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410208510986021553524849 1807656383239516165143637)
                  ·
                    refine ⟨21183473241088080060277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1807656383239516165143637 21183473241088080060277)
                    ·
                      rfl

theorem cell22_61882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_61882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61882 prefixEnd_61882 := by exact prefixLift 61882
  have htrace : WordTrace (prefixWord ++ tailWord_61882) baseStart_61882 baseEnd_61882 := by
    simpa [prefixWord, tailWord_61882, baseEnd_61882] using wordTrace_append hprefix tailTrace_61882
  have hstable : (prefixWord ++ tailWord_61882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61882).length < 2 ^ (prefixWord ++ tailWord_61882).sum := by decide
  have hdescent : baseEnd_61882 < baseStart_61882 := by decide
  rcases family_descends (prefixWord ++ tailWord_61882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61897 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 8]
def baseStart_61897 : Nat := 118140960795 + 61897 * 2 ^ 59
def prefixEnd_61897 : Nat := 4983230072969 + 3 ^ 40 * 61897 * 2
def baseEnd_61897 : Nat := 7062869349211013645077

theorem tailTrace_61897 : CollatzResearch.WordTrace tailWord_61897 prefixEnd_61897 7062869349211013645077 := by
  unfold tailWord_61897
  simp only [CollatzResearch.WordTrace]
  refine ⟨2257569056765215011095945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505046037843476674063963 2257569056765215011095945)
  ·
    refine ⟨1693176792573911258321959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2257569056765215011095945 1693176792573911258321959)
    ·
      refine ⟨2539765188860866887482939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693176792573911258321959 2539765188860866887482939)
      ·
        refine ⟨3809647783291300331224409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539765188860866887482939 3809647783291300331224409)
        ·
          refine ⟨2857235837468475248418307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809647783291300331224409 2857235837468475248418307)
          ·
            refine ⟨4285853756202712872627461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857235837468475248418307 4285853756202712872627461)
            ·
              refine ⟨803597579288008663617649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4285853756202712872627461 803597579288008663617649)
              ·
                refine ⟨602698184466006497713237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803597579288008663617649 602698184466006497713237)
                ·
                  refine ⟨7062869349211013645077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 602698184466006497713237 7062869349211013645077)
                  ·
                    rfl

theorem cell22_61897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_61897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61897 prefixEnd_61897 := by exact prefixLift 61897
  have htrace : WordTrace (prefixWord ++ tailWord_61897) baseStart_61897 baseEnd_61897 := by
    simpa [prefixWord, tailWord_61897, baseEnd_61897] using wordTrace_append hprefix tailTrace_61897
  have hstable : (prefixWord ++ tailWord_61897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61897).length < 2 ^ (prefixWord ++ tailWord_61897).sum := by decide
  have hdescent : baseEnd_61897 < baseStart_61897 := by decide
  rcases family_descends (prefixWord ++ tailWord_61897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_61929 : Nat := 118140960795 + 61929 * 2 ^ 59
def prefixEnd_61929 : Nat := 4983230072969 + 3 ^ 40 * 61929 * 2
def baseEnd_61929 : Nat := 21199562301595624135133

theorem tailTrace_61929 : CollatzResearch.WordTrace tailWord_61929 prefixEnd_61929 21199562301595624135133 := by
  unfold tailWord_61929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258736192649284476260841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505824128432856317507227 2258736192649284476260841)
  ·
    refine ⟨1694052144486963357195631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2258736192649284476260841 1694052144486963357195631)
    ·
      refine ⟨2541078216730445035793447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694052144486963357195631 2541078216730445035793447)
      ·
        refine ⟨3811617325095667553690171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541078216730445035793447 3811617325095667553690171)
        ·
          refine ⟨5717425987643501330535257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811617325095667553690171 5717425987643501330535257)
          ·
            refine ⟨4288069490732625997901443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5717425987643501330535257 4288069490732625997901443)
            ·
              refine ⟨6432104236098938996852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288069490732625997901443 6432104236098938996852165)
              ·
                refine ⟨1206019544268551061909781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6432104236098938996852165 1206019544268551061909781)
                ·
                  refine ⟨56532166137588331027021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1206019544268551061909781 56532166137588331027021)
                  ·
                    refine ⟨21199562301595624135133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56532166137588331027021 21199562301595624135133)
                    ·
                      rfl

theorem cell22_61929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_61929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61929 prefixEnd_61929 := by exact prefixLift 61929
  have htrace : WordTrace (prefixWord ++ tailWord_61929) baseStart_61929 baseEnd_61929 := by
    simpa [prefixWord, tailWord_61929, baseEnd_61929] using wordTrace_append hprefix tailTrace_61929
  have hstable : (prefixWord ++ tailWord_61929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61929).length < 2 ^ (prefixWord ++ tailWord_61929).sum := by decide
  have hdescent : baseEnd_61929 < baseStart_61929 := by decide
  rcases family_descends (prefixWord ++ tailWord_61929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61933 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_61933 : Nat := 118140960795 + 61933 * 2 ^ 59
def prefixEnd_61933 : Nat := 4983230072969 + 3 ^ 40 * 61933 * 2
def baseEnd_61933 : Nat := 21200931583340947035121

theorem tailTrace_61933 : CollatzResearch.WordTrace tailWord_61933 prefixEnd_61933 21200931583340947035121 := by
  unfold tailWord_61933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258882084634793159406453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505921389756528772937635 2258882084634793159406453)
  ·
    refine ⟨211770195434511858694355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2258882084634793159406453 211770195434511858694355)
    ·
      refine ⟨317655293151767788041533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211770195434511858694355 317655293151767788041533)
      ·
        refine ⟨119120734931912920515575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317655293151767788041533 119120734931912920515575)
        ·
          refine ⟨178681102397869380773363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119120734931912920515575 178681102397869380773363)
          ·
            refine ⟨268021653596804071160045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178681102397869380773363 268021653596804071160045)
            ·
              refine ⟨100508120098801526685017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268021653596804071160045 100508120098801526685017)
              ·
                refine ⟨75381090074101145013763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100508120098801526685017 75381090074101145013763)
                ·
                  refine ⟨113071635111151717520645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75381090074101145013763 113071635111151717520645)
                  ·
                    refine ⟨21200931583340947035121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113071635111151717520645 21200931583340947035121)
                    ·
                      rfl

theorem cell22_61933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_61933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61933 prefixEnd_61933 := by exact prefixLift 61933
  have htrace : WordTrace (prefixWord ++ tailWord_61933) baseStart_61933 baseEnd_61933 := by
    simpa [prefixWord, tailWord_61933, baseEnd_61933] using wordTrace_append hprefix tailTrace_61933
  have hstable : (prefixWord ++ tailWord_61933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61933).length < 2 ^ (prefixWord ++ tailWord_61933).sum := by decide
  have hdescent : baseEnd_61933 < baseStart_61933 := by decide
  rcases family_descends (prefixWord ++ tailWord_61933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61959 : List Nat := [1, 1, 4, 3, 3, 10]
def baseStart_61959 : Nat := 118140960795 + 61959 * 2 ^ 59
def prefixEnd_61959 : Nat := 4983230072969 + 3 ^ 40 * 61959 * 2
def baseEnd_61959 : Nat := 261849776724512912161

theorem tailTrace_61959 : CollatzResearch.WordTrace tailWord_61959 prefixEnd_61959 261849776724512912161 := by
  unfold tailWord_61959
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259830382540599599852931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1506553588360399733235287 2259830382540599599852931)
  ·
    refine ⟨3389745573810899399779397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259830382540599599852931 3389745573810899399779397)
    ·
      refine ⟨635577295089543637458637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3389745573810899399779397 635577295089543637458637)
      ·
        refine ⟨238341485658578864046989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635577295089543637458637 238341485658578864046989)
        ·
          refine ⟨89378057121967074017621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238341485658578864046989 89378057121967074017621)
          ·
            refine ⟨261849776724512912161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 89378057121967074017621 261849776724512912161)
            ·
              rfl

theorem cell22_61959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 10].length) (baseStart_61959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61959 prefixEnd_61959 := by exact prefixLift 61959
  have htrace : WordTrace (prefixWord ++ tailWord_61959) baseStart_61959 baseEnd_61959 := by
    simpa [prefixWord, tailWord_61959, baseEnd_61959] using wordTrace_append hprefix tailTrace_61959
  have hstable : (prefixWord ++ tailWord_61959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61959).length < 2 ^ (prefixWord ++ tailWord_61959).sum := by decide
  have hdescent : baseEnd_61959 < baseStart_61959 := by decide
  rcases family_descends (prefixWord ++ tailWord_61959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61963 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 2, 3]
def baseStart_61963 : Nat := 118140960795 + 61963 * 2 ^ 59
def prefixEnd_61963 : Nat := 4983230072969 + 3 ^ 40 * 61963 * 2
def baseEnd_61963 : Nat := 21211201196430868785029

theorem tailTrace_61963 : CollatzResearch.WordTrace tailWord_61963 prefixEnd_61963 21211201196430868785029 := by
  unfold tailWord_61963
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259976274526108282998543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1506650849684072188665695 2259976274526108282998543)
  ·
    refine ⟨3389964411789162424497815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259976274526108282998543 3389964411789162424497815)
    ·
      refine ⟨5084946617683743636746723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389964411789162424497815 5084946617683743636746723)
      ·
        refine ⟨7627419926525615455120085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084946617683743636746723 7627419926525615455120085)
        ·
          refine ⟨178767654527944112229377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7627419926525615455120085 178767654527944112229377)
          ·
            refine ⟨134075740895958084172033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178767654527944112229377 134075740895958084172033)
            ·
              refine ⟨100556805671968563129025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134075740895958084172033 100556805671968563129025)
              ·
                refine ⟨75417604253976422346769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100556805671968563129025 75417604253976422346769)
                ·
                  refine ⟨56563203190482316760077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75417604253976422346769 56563203190482316760077)
                  ·
                    refine ⟨21211201196430868785029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56563203190482316760077 21211201196430868785029)
                    ·
                      rfl

theorem cell22_61963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].length) (baseStart_61963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61963 prefixEnd_61963 := by exact prefixLift 61963
  have htrace : WordTrace (prefixWord ++ tailWord_61963) baseStart_61963 baseEnd_61963 := by
    simpa [prefixWord, tailWord_61963, baseEnd_61963] using wordTrace_append hprefix tailTrace_61963
  have hstable : (prefixWord ++ tailWord_61963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61963).length < 2 ^ (prefixWord ++ tailWord_61963).sum := by decide
  have hdescent : baseEnd_61963 < baseStart_61963 := by decide
  rcases family_descends (prefixWord ++ tailWord_61963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61976 : List Nat := [2, 1, 2, 3, 3, 3, 1, 7]
def baseStart_61976 : Nat := 118140960795 + 61976 * 2 ^ 59
def prefixEnd_61976 : Nat := 4983230072969 + 3 ^ 40 * 61976 * 2
def baseEnd_61976 : Nat := 2357294595789240912221

theorem tailTrace_61976 : CollatzResearch.WordTrace tailWord_61976 prefixEnd_61976 2357294595789240912221 := by
  unfold tailWord_61976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130225211739505751610891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1506966948986007668814521 1130225211739505751610891)
  ·
    refine ⟨1695337817609258627416337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1130225211739505751610891 1695337817609258627416337)
    ·
      refine ⟨1271503363206943970562253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1695337817609258627416337 1271503363206943970562253)
      ·
        refine ⟨476813761202603988960845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1271503363206943970562253 476813761202603988960845)
        ·
          refine ⟨178805160450976495860317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476813761202603988960845 178805160450976495860317)
          ·
            refine ⟨67051935169116185947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178805160450976495860317 67051935169116185947619)
            ·
              refine ⟨100577902753674278921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67051935169116185947619 100577902753674278921429)
              ·
                refine ⟨2357294595789240912221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100577902753674278921429 2357294595789240912221)
                ·
                  rfl

theorem cell22_61976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_61976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_61976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_61976 prefixEnd_61976 := by exact prefixLift 61976
  have htrace : WordTrace (prefixWord ++ tailWord_61976) baseStart_61976 baseEnd_61976 := by
    simpa [prefixWord, tailWord_61976, baseEnd_61976] using wordTrace_append hprefix tailTrace_61976
  have hstable : (prefixWord ++ tailWord_61976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61976).length < 2 ^ (prefixWord ++ tailWord_61976).sum := by decide
  have hdescent : baseEnd_61976 < baseStart_61976 := by decide
  rcases family_descends (prefixWord ++ tailWord_61976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62014 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_62014 : Nat := 118140960795 + 62014 * 2 ^ 59
def prefixEnd_62014 : Nat := 4983230072969 + 3 ^ 40 * 62014 * 2
def baseEnd_62014 : Nat := 21228659538683735759873

theorem tailTrace_62014 : CollatzResearch.WordTrace tailWord_62014 prefixEnd_62014 21228659538683735759873 := by
  unfold tailWord_62014
  simp only [CollatzResearch.WordTrace]
  refine ⟨282729549667667999138137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1507890931560895995403397 282729549667667999138137)
  ·
    refine ⟨212047162250750999353603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282729549667667999138137 212047162250750999353603)
    ·
      refine ⟨318070743376126499030405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212047162250750999353603 318070743376126499030405)
      ·
        refine ⟨59638264383023718568201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318070743376126499030405 59638264383023718568201)
        ·
          refine ⟨44728698287267788926151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59638264383023718568201 44728698287267788926151)
          ·
            refine ⟨67093047430901683389227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44728698287267788926151 67093047430901683389227)
            ·
              refine ⟨100639571146352525083841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67093047430901683389227 100639571146352525083841)
              ·
                refine ⟨75479678359764393812881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100639571146352525083841 75479678359764393812881)
                ·
                  refine ⟨56609758769823295359661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75479678359764393812881 56609758769823295359661)
                  ·
                    refine ⟨21228659538683735759873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56609758769823295359661 21228659538683735759873)
                    ·
                      rfl

theorem cell22_62014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_62014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62014 prefixEnd_62014 := by exact prefixLift 62014
  have htrace : WordTrace (prefixWord ++ tailWord_62014) baseStart_62014 baseEnd_62014 := by
    simpa [prefixWord, tailWord_62014, baseEnd_62014] using wordTrace_append hprefix tailTrace_62014
  have hstable : (prefixWord ++ tailWord_62014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62014).length < 2 ^ (prefixWord ++ tailWord_62014).sum := by decide
  have hdescent : baseEnd_62014 < baseStart_62014 := by decide
  rcases family_descends (prefixWord ++ tailWord_62014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62021 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 5]
def baseStart_62021 : Nat := 118140960795 + 62021 * 2 ^ 59
def prefixEnd_62021 : Nat := 4983230072969 + 3 ^ 40 * 62021 * 2
def baseEnd_62021 : Nat := 7077018593912683611617

theorem tailTrace_62021 : CollatzResearch.WordTrace tailWord_62021 prefixEnd_62021 7077018593912683611617 := by
  unfold tailWord_62021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262091708315984188609917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1508061138877322792406611 2262091708315984188609917)
  ·
    refine ⟨848284390618494070728719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2262091708315984188609917 848284390618494070728719)
    ·
      refine ⟨1272426585927741106093079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848284390618494070728719 1272426585927741106093079)
      ·
        refine ⟨1908639878891611659139619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272426585927741106093079 1908639878891611659139619)
        ·
          refine ⟨2862959818337417488709429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908639878891611659139619 2862959818337417488709429)
          ·
            refine ⟨268402482969132889566509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2862959818337417488709429 268402482969132889566509)
            ·
              refine ⟨100650931113424833587441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268402482969132889566509 100650931113424833587441)
              ·
                refine ⟨75488198335068625190581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100650931113424833587441 75488198335068625190581)
                ·
                  refine ⟨7077018593912683611617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75488198335068625190581 7077018593912683611617)
                  ·
                    rfl

theorem cell22_62021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_62021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62021 prefixEnd_62021 := by exact prefixLift 62021
  have htrace : WordTrace (prefixWord ++ tailWord_62021) baseStart_62021 baseEnd_62021 := by
    simpa [prefixWord, tailWord_62021, baseEnd_62021] using wordTrace_append hprefix tailTrace_62021
  have hstable : (prefixWord ++ tailWord_62021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62021).length < 2 ^ (prefixWord ++ tailWord_62021).sum := by decide
  have hdescent : baseEnd_62021 < baseStart_62021 := by decide
  rcases family_descends (prefixWord ++ tailWord_62021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62036 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_62036 : Nat := 118140960795 + 62036 * 2 ^ 59
def prefixEnd_62036 : Nat := 4983230072969 + 3 ^ 40 * 62036 * 2
def baseEnd_62036 : Nat := 21236190588283011709805

theorem tailTrace_62036 : CollatzResearch.WordTrace tailWord_62036 prefixEnd_62036 21236190588283011709805 := by
  unfold tailWord_62036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131319401630820875202981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1508425868841094500270641 1131319401630820875202981)
  ·
    refine ⟨212122387805778914100559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1131319401630820875202981 212122387805778914100559)
    ·
      refine ⟨318183581708668371150839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212122387805778914100559 318183581708668371150839)
      ·
        refine ⟨477275372563002556726259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318183581708668371150839 477275372563002556726259)
        ·
          refine ⟨715913058844503835089389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477275372563002556726259 715913058844503835089389)
          ·
            refine ⟨268467397066688938158521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715913058844503835089389 268467397066688938158521)
            ·
              refine ⟨201350547800016703618891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268467397066688938158521 201350547800016703618891)
              ·
                refine ⟨302025821700025055428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201350547800016703618891 302025821700025055428337)
                ·
                  refine ⟨226519366275018791571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302025821700025055428337 226519366275018791571253)
                  ·
                    refine ⟨21236190588283011709805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226519366275018791571253 21236190588283011709805)
                    ·
                      rfl

theorem cell22_62036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_62036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62036 prefixEnd_62036 := by exact prefixLift 62036
  have htrace : WordTrace (prefixWord ++ tailWord_62036) baseStart_62036 baseEnd_62036 := by
    simpa [prefixWord, tailWord_62036, baseEnd_62036] using wordTrace_append hprefix tailTrace_62036
  have hstable : (prefixWord ++ tailWord_62036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62036).length < 2 ^ (prefixWord ++ tailWord_62036).sum := by decide
  have hdescent : baseEnd_62036 < baseStart_62036 := by decide
  rcases family_descends (prefixWord ++ tailWord_62036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62079 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_62079 : Nat := 118140960795 + 62079 * 2 ^ 59
def prefixEnd_62079 : Nat := 4983230072969 + 3 ^ 40 * 62079 * 2
def baseEnd_62079 : Nat := 21250910367045232884673

theorem tailTrace_62079 : CollatzResearch.WordTrace tailWord_62079 prefixEnd_62079 21250910367045232884673 := by
  unfold tailWord_62079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264207142105860094221291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1509471428070573396147527 2264207142105860094221291)
  ·
    refine ⟨3396310713158790141331937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2264207142105860094221291 3396310713158790141331937)
    ·
      refine ⟨2547233034869092605998953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3396310713158790141331937 2547233034869092605998953)
      ·
        refine ⟨1910424776151819454499215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547233034869092605998953 1910424776151819454499215)
        ·
          refine ⟨2865637164227729181748823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910424776151819454499215 2865637164227729181748823)
          ·
            refine ⟨4298455746341593772623235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865637164227729181748823 4298455746341593772623235)
            ·
              refine ⟨6447683619512390658934853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298455746341593772623235 6447683619512390658934853)
              ·
                refine ⟨1208940678658573248550285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6447683619512390658934853 1208940678658573248550285)
                ·
                  refine ⟨453352754496964968206357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208940678658573248550285 453352754496964968206357)
                  ·
                    refine ⟨21250910367045232884673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 453352754496964968206357 21250910367045232884673)
                    ·
                      rfl

theorem cell22_62079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_62079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62079 prefixEnd_62079 := by exact prefixLift 62079
  have htrace : WordTrace (prefixWord ++ tailWord_62079) baseStart_62079 baseEnd_62079 := by
    simpa [prefixWord, tailWord_62079, baseEnd_62079] using wordTrace_append hprefix tailTrace_62079
  have hstable : (prefixWord ++ tailWord_62079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62079).length < 2 ^ (prefixWord ++ tailWord_62079).sum := by decide
  have hdescent : baseEnd_62079 < baseStart_62079 := by decide
  rcases family_descends (prefixWord ++ tailWord_62079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62141 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_62141 : Nat := 118140960795 + 62141 * 2 ^ 59
def prefixEnd_62141 : Nat := 4983230072969 + 3 ^ 40 * 62141 * 2
def baseEnd_62141 : Nat := 21272134234097737834483

theorem tailTrace_62141 : CollatzResearch.WordTrace tailWord_62141 prefixEnd_62141 21272134234097737834483 := by
  unfold tailWord_62141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266468467881244682978277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1510978978587496455318851 2266468467881244682978277)
  ·
    refine ⟨424962837727733378058427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2266468467881244682978277 424962837727733378058427)
    ·
      refine ⟨637444256591600067087641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424962837727733378058427 637444256591600067087641)
      ·
        refine ⟨478083192443700050315731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 637444256591600067087641 478083192443700050315731)
        ·
          refine ⟨717124788665550075473597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478083192443700050315731 717124788665550075473597)
          ·
            refine ⟨268921795749581278302599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717124788665550075473597 268921795749581278302599)
            ·
              refine ⟨403382693624371917453899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268921795749581278302599 403382693624371917453899)
              ·
                refine ⟨605074040436557876180849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403382693624371917453899 605074040436557876180849)
                ·
                  refine ⟨453805530327418407135637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605074040436557876180849 453805530327418407135637)
                  ·
                    refine ⟨21272134234097737834483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 453805530327418407135637 21272134234097737834483)
                    ·
                      rfl

theorem cell22_62141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_62141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62141 prefixEnd_62141 := by exact prefixLift 62141
  have htrace : WordTrace (prefixWord ++ tailWord_62141) baseStart_62141 baseEnd_62141 := by
    simpa [prefixWord, tailWord_62141, baseEnd_62141] using wordTrace_append hprefix tailTrace_62141
  have hstable : (prefixWord ++ tailWord_62141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62141).length < 2 ^ (prefixWord ++ tailWord_62141).sum := by decide
  have hdescent : baseEnd_62141 < baseStart_62141 := by decide
  rcases family_descends (prefixWord ++ tailWord_62141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62177 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 1, 3]
def baseStart_62177 : Nat := 118140960795 + 62177 * 2 ^ 59
def prefixEnd_62177 : Nat := 4983230072969 + 3 ^ 40 * 62177 * 2
def baseEnd_62177 : Nat := 21284457769805643934373

theorem tailTrace_62177 : CollatzResearch.WordTrace tailWord_62177 prefixEnd_62177 21284457769805643934373 := by
  unfold tailWord_62177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267781495750822831288785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1511854330500548554192523 2267781495750822831288785)
  ·
    refine ⟨1700836121813117123466589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267781495750822831288785 1700836121813117123466589)
    ·
      refine ⟨637813545679918921299971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1700836121813117123466589 637813545679918921299971)
      ·
        refine ⟨956720318519878381949957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637813545679918921299971 956720318519878381949957)
        ·
          refine ⟨179385059722477196615617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 956720318519878381949957 179385059722477196615617)
          ·
            refine ⟨134538794791857897461713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179385059722477196615617 134538794791857897461713)
            ·
              refine ⟨100904096093893423096285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134538794791857897461713 100904096093893423096285)
              ·
                refine ⟨37839036035210033661107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100904096093893423096285 37839036035210033661107)
                ·
                  refine ⟨56758554052815050491661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37839036035210033661107 56758554052815050491661)
                  ·
                    refine ⟨21284457769805643934373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56758554052815050491661 21284457769805643934373)
                    ·
                      rfl

theorem cell22_62177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_62177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62177 prefixEnd_62177 := by exact prefixLift 62177
  have htrace : WordTrace (prefixWord ++ tailWord_62177) baseStart_62177 baseEnd_62177 := by
    simpa [prefixWord, tailWord_62177, baseEnd_62177] using wordTrace_append hprefix tailTrace_62177
  have hstable : (prefixWord ++ tailWord_62177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62177).length < 2 ^ (prefixWord ++ tailWord_62177).sum := by decide
  have hdescent : baseEnd_62177 < baseStart_62177 := by decide
  rcases family_descends (prefixWord ++ tailWord_62177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62190 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_62190 : Nat := 118140960795 + 62190 * 2 ^ 59
def prefixEnd_62190 : Nat := 4983230072969 + 3 ^ 40 * 62190 * 2
def baseEnd_62190 : Nat := 7096302645159314453111

theorem tailTrace_62190 : CollatzResearch.WordTrace tailWord_62190 prefixEnd_62190 7096302645159314453111 := by
  unfold tailWord_62190
  simp only [CollatzResearch.WordTrace]
  refine ⟨283531955587965756439003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1512170429802484034341349 283531955587965756439003)
  ·
    refine ⟨425297933381948634658505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283531955587965756439003 425297933381948634658505)
    ·
      refine ⟨318973450036461475993879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425297933381948634658505 318973450036461475993879)
      ·
        refine ⟨478460175054692213990819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318973450036461475993879 478460175054692213990819)
        ·
          refine ⟨717690262582038320986229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478460175054692213990819 717690262582038320986229)
          ·
            refine ⟨67283462117066092592459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 717690262582038320986229 67283462117066092592459)
            ·
              refine ⟨100925193175599138888689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67283462117066092592459 100925193175599138888689)
              ·
                refine ⟨75693894881699354166517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100925193175599138888689 75693894881699354166517)
                ·
                  refine ⟨7096302645159314453111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75693894881699354166517 7096302645159314453111)
                  ·
                    rfl

theorem cell22_62190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_62190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62190 prefixEnd_62190 := by exact prefixLift 62190
  have htrace : WordTrace (prefixWord ++ tailWord_62190) baseStart_62190 baseEnd_62190 := by
    simpa [prefixWord, tailWord_62190, baseEnd_62190] using wordTrace_append hprefix tailTrace_62190
  have hstable : (prefixWord ++ tailWord_62190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62190).length < 2 ^ (prefixWord ++ tailWord_62190).sum := by decide
  have hdescent : baseEnd_62190 < baseStart_62190 := by decide
  rcases family_descends (prefixWord ++ tailWord_62190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62291 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 9]
def baseStart_62291 : Nat := 118140960795 + 62291 * 2 ^ 59
def prefixEnd_62291 : Nat := 4983230072969 + 3 ^ 40 * 62291 * 2
def baseEnd_62291 : Nat := 7107827433182448861341

theorem tailTrace_62291 : CollatzResearch.WordTrace tailWord_62291 prefixEnd_62291 7107827433182448861341 := by
  unfold tailWord_62291
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271939417337820300938727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1514626278225213533959151 2271939417337820300938727)
  ·
    refine ⟨3407909126006730451408091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271939417337820300938727 3407909126006730451408091)
    ·
      refine ⟨5111863689010095677112137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407909126006730451408091 5111863689010095677112137)
      ·
        refine ⟨3833897766757571757834103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5111863689010095677112137 3833897766757571757834103)
        ·
          refine ⟨5750846650136357636751155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833897766757571757834103 5750846650136357636751155)
          ·
            refine ⟨8626269975204536455126733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750846650136357636751155 8626269975204536455126733)
            ·
              refine ⟨3234851240701701170672525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8626269975204536455126733 3234851240701701170672525)
              ·
                refine ⟨1213069215263137939002197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3234851240701701170672525 1213069215263137939002197)
                ·
                  refine ⟨7107827433182448861341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1213069215263137939002197 7107827433182448861341)
                  ·
                    rfl

theorem cell22_62291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_62291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62291 prefixEnd_62291 := by exact prefixLift 62291
  have htrace : WordTrace (prefixWord ++ tailWord_62291) baseStart_62291 baseEnd_62291 := by
    simpa [prefixWord, tailWord_62291, baseEnd_62291] using wordTrace_append hprefix tailTrace_62291
  have hstable : (prefixWord ++ tailWord_62291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62291).length < 2 ^ (prefixWord ++ tailWord_62291).sum := by decide
  have hdescent : baseEnd_62291 < baseStart_62291 := by decide
  rcases family_descends (prefixWord ++ tailWord_62291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62325 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 5]
def baseStart_62325 : Nat := 118140960795 + 62325 * 2 ^ 59
def prefixEnd_62325 : Nat := 4983230072969 + 3 ^ 40 * 62325 * 2
def baseEnd_62325 : Nat := 7111707064794197077973

theorem tailTrace_62325 : CollatzResearch.WordTrace tailWord_62325 prefixEnd_62325 7111707064794197077973 := by
  unfold tailWord_62325
  simp only [CollatzResearch.WordTrace]
  refine ⟨2273179499214644107676429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1515452999476429405117619 2273179499214644107676429)
  ·
    refine ⟨852442312205491540378661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2273179499214644107676429 852442312205491540378661)
    ·
      refine ⟨159832933538529663820999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 852442312205491540378661 159832933538529663820999)
      ·
        refine ⟨239749400307794495731499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159832933538529663820999 239749400307794495731499)
        ·
          refine ⟨359624100461691743597249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239749400307794495731499 359624100461691743597249)
          ·
            refine ⟨269718075346268807697937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359624100461691743597249 269718075346268807697937)
            ·
              refine ⟨202288556509701605773453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269718075346268807697937 202288556509701605773453)
              ·
                refine ⟨75858208691138102165045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202288556509701605773453 75858208691138102165045)
                ·
                  refine ⟨7111707064794197077973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75858208691138102165045 7111707064794197077973)
                  ·
                    rfl

theorem cell22_62325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_62325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62325 prefixEnd_62325 := by exact prefixLift 62325
  have htrace : WordTrace (prefixWord ++ tailWord_62325) baseStart_62325 baseEnd_62325 := by
    simpa [prefixWord, tailWord_62325, baseEnd_62325] using wordTrace_append hprefix tailTrace_62325
  have hstable : (prefixWord ++ tailWord_62325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62325).length < 2 ^ (prefixWord ++ tailWord_62325).sum := by decide
  have hdescent : baseEnd_62325 < baseStart_62325 := by decide
  rcases family_descends (prefixWord ++ tailWord_62325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62368 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_62368 : Nat := 118140960795 + 62368 * 2 ^ 59
def prefixEnd_62368 : Nat := 4983230072969 + 3 ^ 40 * 62368 * 2
def baseEnd_62368 : Nat := 21349840973144812408787

theorem tailTrace_62368 : CollatzResearch.WordTrace tailWord_62368 prefixEnd_62368 21349840973144812408787 := by
  unfold tailWord_62368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137373919029431225745879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1516498558705908300994505 1137373919029431225745879)
  ·
    refine ⟨1706060878544146838618819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1137373919029431225745879 1706060878544146838618819)
    ·
      refine ⟨2559091317816220257928229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706060878544146838618819 2559091317816220257928229)
      ·
        refine ⟨479829622090541298361543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2559091317816220257928229 479829622090541298361543)
        ·
          refine ⟨719744433135811947542315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479829622090541298361543 719744433135811947542315)
          ·
            refine ⟨1079616649703717921313473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719744433135811947542315 1079616649703717921313473)
            ·
              refine ⟨809712487277788440985105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079616649703717921313473 809712487277788440985105)
              ·
                refine ⟨607284365458341330738829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809712487277788440985105 607284365458341330738829)
                ·
                  refine ⟨227731637046877999027061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607284365458341330738829 227731637046877999027061)
                  ·
                    refine ⟨21349840973144812408787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227731637046877999027061 21349840973144812408787)
                    ·
                      rfl

theorem cell22_62368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_62368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62368 prefixEnd_62368 := by exact prefixLift 62368
  have htrace : WordTrace (prefixWord ++ tailWord_62368) baseStart_62368 baseEnd_62368 := by
    simpa [prefixWord, tailWord_62368, baseEnd_62368] using wordTrace_append hprefix tailTrace_62368
  have hstable : (prefixWord ++ tailWord_62368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62368).length < 2 ^ (prefixWord ++ tailWord_62368).sum := by decide
  have hdescent : baseEnd_62368 < baseStart_62368 := by decide
  rcases family_descends (prefixWord ++ tailWord_62368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62370 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_62370 : Nat := 118140960795 + 62370 * 2 ^ 59
def prefixEnd_62370 : Nat := 4983230072969 + 3 ^ 40 * 62370 * 2
def baseEnd_62370 : Nat := 7116841871339157952927

theorem tailTrace_62370 : CollatzResearch.WordTrace tailWord_62370 prefixEnd_62370 7116841871339157952927 := by
  unfold tailWord_62370
  simp only [CollatzResearch.WordTrace]
  refine ⟨568705196012904198266141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1516547189367744528709709 568705196012904198266141)
  ·
    refine ⟨213264448504839074349803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 568705196012904198266141 213264448504839074349803)
    ·
      refine ⟨319896672757258611524705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213264448504839074349803 319896672757258611524705)
      ·
        refine ⟨239922504567943958643529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319896672757258611524705 239922504567943958643529)
        ·
          refine ⟨179941878425957968982647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239922504567943958643529 179941878425957968982647)
          ·
            refine ⟨269912817638936953473971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179941878425957968982647 269912817638936953473971)
            ·
              refine ⟨404869226458405430210957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269912817638936953473971 404869226458405430210957)
              ·
                refine ⟨151825959921902036329109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404869226458405430210957 151825959921902036329109)
                ·
                  refine ⟨7116841871339157952927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151825959921902036329109 7116841871339157952927)
                  ·
                    rfl

theorem cell22_62370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_62370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62370 prefixEnd_62370 := by exact prefixLift 62370
  have htrace : WordTrace (prefixWord ++ tailWord_62370) baseStart_62370 baseEnd_62370 := by
    simpa [prefixWord, tailWord_62370, baseEnd_62370] using wordTrace_append hprefix tailTrace_62370
  have hstable : (prefixWord ++ tailWord_62370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62370).length < 2 ^ (prefixWord ++ tailWord_62370).sum := by decide
  have hdescent : baseEnd_62370 < baseStart_62370 := by decide
  rcases family_descends (prefixWord ++ tailWord_62370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
