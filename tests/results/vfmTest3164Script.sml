Theory vfmTest3164[no_sig_docs]
Ancestors vfmTestDefs3164
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3164_0.nsv", "result3164_1.nsv"];
val thyn = "vfmTestDefs3164";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
