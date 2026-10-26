Theory vfmTest3077[no_sig_docs]
Ancestors vfmTestDefs3077
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3077_0.nsv", "result3077_1.nsv", "result3077_2.nsv", "result3077_3.nsv"];
val thyn = "vfmTestDefs3077";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
