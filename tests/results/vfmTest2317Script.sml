Theory vfmTest2317[no_sig_docs]
Ancestors vfmTestDefs2317
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2317_0.nsv", "result2317_1.nsv", "result2317_2.nsv", "result2317_3.nsv", "result2317_4.nsv", "result2317_5.nsv", "result2317_6.nsv", "result2317_7.nsv"];
val thyn = "vfmTestDefs2317";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
