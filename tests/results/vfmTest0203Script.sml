Theory vfmTest0203[no_sig_docs]
Ancestors vfmTestDefs0203
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0203_0.nsv", "result0203_1.nsv", "result0203_2.nsv"];
val thyn = "vfmTestDefs0203";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
