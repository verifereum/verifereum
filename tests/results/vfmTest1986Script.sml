Theory vfmTest1986[no_sig_docs]
Ancestors vfmTestDefs1986
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1986_0.nsv", "result1986_1.nsv", "result1986_2.nsv", "result1986_3.nsv"];
val thyn = "vfmTestDefs1986";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
