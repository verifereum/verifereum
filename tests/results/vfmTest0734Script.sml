Theory vfmTest0734[no_sig_docs]
Ancestors vfmTestDefs0734
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0734_0.nsv", "result0734_1.nsv", "result0734_2.nsv", "result0734_3.nsv"];
val thyn = "vfmTestDefs0734";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
