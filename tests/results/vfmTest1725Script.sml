Theory vfmTest1725[no_sig_docs]
Ancestors vfmTestDefs1725
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1725_0.nsv", "result1725_1.nsv", "result1725_2.nsv", "result1725_3.nsv"];
val thyn = "vfmTestDefs1725";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
