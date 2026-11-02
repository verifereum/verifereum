Theory vfmTest3118[no_sig_docs]
Ancestors vfmTestDefs3118
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3118_0.nsv", "result3118_1.nsv", "result3118_2.nsv", "result3118_3.nsv", "result3118_4.nsv", "result3118_5.nsv", "result3118_6.nsv"];
val thyn = "vfmTestDefs3118";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
