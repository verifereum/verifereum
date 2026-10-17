Theory vfmTest0161[no_sig_docs]
Ancestors vfmTestDefs0161
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0161_0.nsv", "result0161_1.nsv", "result0161_2.nsv", "result0161_3.nsv", "result0161_4.nsv"];
val thyn = "vfmTestDefs0161";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
