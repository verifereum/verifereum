Theory vfmTest2246[no_sig_docs]
Ancestors vfmTestDefs2246
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2246_0.nsv", "result2246_1.nsv", "result2246_2.nsv", "result2246_3.nsv", "result2246_4.nsv", "result2246_5.nsv"];
val thyn = "vfmTestDefs2246";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
