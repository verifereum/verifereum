Theory vfmTest3145[no_sig_docs]
Ancestors vfmTestDefs3145
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3145_0.nsv", "result3145_1.nsv", "result3145_2.nsv", "result3145_3.nsv"];
val thyn = "vfmTestDefs3145";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
