Theory vfmTest2253[no_sig_docs]
Ancestors vfmTestDefs2253
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2253_0.nsv", "result2253_1.nsv", "result2253_2.nsv", "result2253_3.nsv", "result2253_4.nsv", "result2253_5.nsv"];
val thyn = "vfmTestDefs2253";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
