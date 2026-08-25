Theory vfmTest0191[no_sig_docs]
Ancestors vfmTestDefs0191
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0191_0.nsv", "result0191_1.nsv", "result0191_2.nsv"];
val thyn = "vfmTestDefs0191";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
