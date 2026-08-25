Theory vfmTest0360[no_sig_docs]
Ancestors vfmTestDefs0360
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0360_0.nsv", "result0360_1.nsv", "result0360_2.nsv", "result0360_3.nsv", "result0360_4.nsv"];
val thyn = "vfmTestDefs0360";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
