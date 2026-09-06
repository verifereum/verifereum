Theory vfmTest2389[no_sig_docs]
Ancestors vfmTestDefs2389
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2389_0.nsv", "result2389_1.nsv", "result2389_2.nsv", "result2389_3.nsv", "result2389_4.nsv", "result2389_5.nsv", "result2389_6.nsv", "result2389_7.nsv"];
val thyn = "vfmTestDefs2389";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
