Theory vfmTest0575[no_sig_docs]
Ancestors vfmTestDefs0575
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0575_0.nsv", "result0575_1.nsv"];
val thyn = "vfmTestDefs0575";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
