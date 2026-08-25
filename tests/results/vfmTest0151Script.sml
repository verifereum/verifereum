Theory vfmTest0151[no_sig_docs]
Ancestors vfmTestDefs0151
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0151_0.nsv", "result0151_1.nsv", "result0151_2.nsv"];
val thyn = "vfmTestDefs0151";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
