Theory vfmTest2604[no_sig_docs]
Ancestors vfmTestDefs2604
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2604_0.nsv", "result2604_1.nsv", "result2604_2.nsv", "result2604_3.nsv"];
val thyn = "vfmTestDefs2604";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
