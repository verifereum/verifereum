Theory vfmTest2786[no_sig_docs]
Ancestors vfmTestDefs2786
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2786_0.nsv", "result2786_1.nsv", "result2786_2.nsv", "result2786_3.nsv"];
val thyn = "vfmTestDefs2786";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
