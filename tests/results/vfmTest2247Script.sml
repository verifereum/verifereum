Theory vfmTest2247[no_sig_docs]
Ancestors vfmTestDefs2247
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2247_0.nsv", "result2247_1.nsv", "result2247_2.nsv", "result2247_3.nsv", "result2247_4.nsv"];
val thyn = "vfmTestDefs2247";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
