Theory vfmTest1952[no_sig_docs]
Ancestors vfmTestDefs1952
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1952_0.nsv", "result1952_1.nsv", "result1952_2.nsv", "result1952_3.nsv"];
val thyn = "vfmTestDefs1952";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
