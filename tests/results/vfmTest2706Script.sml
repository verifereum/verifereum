Theory vfmTest2706[no_sig_docs]
Ancestors vfmTestDefs2706
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2706_0.nsv", "result2706_1.nsv", "result2706_2.nsv", "result2706_3.nsv"];
val thyn = "vfmTestDefs2706";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
