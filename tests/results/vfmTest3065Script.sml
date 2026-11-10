Theory vfmTest3065[no_sig_docs]
Ancestors vfmTestDefs3065
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3065_0.nsv", "result3065_1.nsv", "result3065_2.nsv", "result3065_3.nsv"];
val thyn = "vfmTestDefs3065";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
