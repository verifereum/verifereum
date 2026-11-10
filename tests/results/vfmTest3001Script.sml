Theory vfmTest3001[no_sig_docs]
Ancestors vfmTestDefs3001
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3001_0.nsv", "result3001_1.nsv", "result3001_2.nsv", "result3001_3.nsv", "result3001_4.nsv", "result3001_5.nsv", "result3001_6.nsv", "result3001_7.nsv"];
val thyn = "vfmTestDefs3001";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
