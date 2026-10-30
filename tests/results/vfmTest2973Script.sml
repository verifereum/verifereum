Theory vfmTest2973[no_sig_docs]
Ancestors vfmTestDefs2973
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2973_0.nsv", "result2973_1.nsv", "result2973_2.nsv", "result2973_3.nsv", "result2973_4.nsv", "result2973_5.nsv"];
val thyn = "vfmTestDefs2973";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
