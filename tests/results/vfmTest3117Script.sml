Theory vfmTest3117[no_sig_docs]
Ancestors vfmTestDefs3117
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3117_0.nsv", "result3117_1.nsv", "result3117_2.nsv"];
val thyn = "vfmTestDefs3117";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
