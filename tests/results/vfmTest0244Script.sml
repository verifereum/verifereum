Theory vfmTest0244[no_sig_docs]
Ancestors vfmTestDefs0244
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0244_0.nsv", "result0244_1.nsv", "result0244_2.nsv", "result0244_3.nsv", "result0244_4.nsv", "result0244_5.nsv", "result0244_6.nsv", "result0244_7.nsv"];
val thyn = "vfmTestDefs0244";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
