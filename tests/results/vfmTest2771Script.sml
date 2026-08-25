Theory vfmTest2771[no_sig_docs]
Ancestors vfmTestDefs2771
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2771_0.nsv", "result2771_1.nsv", "result2771_2.nsv", "result2771_3.nsv"];
val thyn = "vfmTestDefs2771";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
