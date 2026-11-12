Theory vfmTest2141[no_sig_docs]
Ancestors vfmTestDefs2141
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2141_0.nsv", "result2141_1.nsv", "result2141_2.nsv", "result2141_3.nsv", "result2141_4.nsv", "result2141_5.nsv"];
val thyn = "vfmTestDefs2141";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
