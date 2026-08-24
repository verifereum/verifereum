Theory vfmTest0258[no_sig_docs]
Ancestors vfmTestDefs0258
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0258_0.nsv", "result0258_1.nsv", "result0258_2.nsv", "result0258_3.nsv", "result0258_4.nsv", "result0258_5.nsv", "result0258_6.nsv"];
val thyn = "vfmTestDefs0258";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
