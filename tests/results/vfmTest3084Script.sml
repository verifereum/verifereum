Theory vfmTest3084[no_sig_docs]
Ancestors vfmTestDefs3084
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3084_0.nsv", "result3084_1.nsv"];
val thyn = "vfmTestDefs3084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
