Theory vfmTest2370[no_sig_docs]
Ancestors vfmTestDefs2370
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2370_0.nsv", "result2370_1.nsv", "result2370_2.nsv", "result2370_3.nsv", "result2370_4.nsv", "result2370_5.nsv", "result2370_6.nsv", "result2370_7.nsv"];
val thyn = "vfmTestDefs2370";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
