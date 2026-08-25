Theory vfmTest0150[no_sig_docs]
Ancestors vfmTestDefs0150
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0150_0.nsv", "result0150_1.nsv", "result0150_2.nsv", "result0150_3.nsv"];
val thyn = "vfmTestDefs0150";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
