Theory vfmTest3080[no_sig_docs]
Ancestors vfmTestDefs3080
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3080_0.nsv", "result3080_1.nsv", "result3080_2.nsv"];
val thyn = "vfmTestDefs3080";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
