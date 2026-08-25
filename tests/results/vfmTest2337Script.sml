Theory vfmTest2337[no_sig_docs]
Ancestors vfmTestDefs2337
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2337_0.nsv", "result2337_1.nsv", "result2337_2.nsv"];
val thyn = "vfmTestDefs2337";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
