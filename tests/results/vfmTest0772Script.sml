Theory vfmTest0772[no_sig_docs]
Ancestors vfmTestDefs0772
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0772_0.nsv", "result0772_1.nsv", "result0772_2.nsv", "result0772_3.nsv", "result0772_4.nsv", "result0772_5.nsv"];
val thyn = "vfmTestDefs0772";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
